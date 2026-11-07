(* When EffCaml's coercion of a recursive call made under a handler is sound.

   The translation (see [Cgen], method [f_var]) translates a reference to a
   function of the current [let rec] that occurs inside a handled body as a
   coercion: the callee is run with the handlers *outside* the innermost
   enclosing handler, and its result is passed on to that handler's
   continuation.  The callee's operations therefore bypass the clauses of that
   handler.  This is exact only when every operation that can escape the
   callee is handled by a clause of that handler that forwards it unchanged
   ([let r = perform (Op x..) in continue k r], or
   [continue k (perform (Op x..))]): forwarding through the clause and going
   to the outer handler directly are then the same.  A clause that answers the
   operation itself, or does anything besides forwarding it, is skipped, and
   the translation then describes a different program -- one whose model
   checking can answer [sat] for a program that violates its property.

   [check] decides that condition syntactically, conservatively, before any
   translation:
   - the operations that may escape a recursive function are over-approximated
     by a fixpoint over its body: [perform]/[perform_atp] of a constructor
     contributes it; a handler application contributes its body's operations
     minus the handler's clauses, plus whatever its clauses and return clause
     perform; a call of the function itself contributes the current estimate;
     a call of any other function that is not a total primitive makes the
     estimate "every operation";
   - a reference to the function inside a handled body is accepted only along
     a direct path from that body (through [let], sequencing, [if],
     applications, tuples and constructors), under exactly one handler of the
     same definition, and only when that handler forwards every operation of
     the estimate it has a clause for.
   Anything else inside a handled body that mentions the function -- a nested
   [fun], a second handler, a handler that is not a record literal -- is
   rejected.  The check only adds refusals: when it accepts, the coercion is
   the translation of the program; when it rejects, nothing is translated. *)

open Core
open Typedtree

type ops = Every | Ops of String.Set.t

let none = Ops String.Set.empty

let union a b =
  match (a, b) with
  | Every, _ | _, Every -> Every
  | Ops x, Ops y -> Ops (Set.union x y)

let union_list = List.fold ~init:none ~f:union

let ops_equal a b =
  match (a, b) with
  | Every, Every -> true
  | Ops x, Ops y -> Set.equal x y
  | _ -> false

let strip_stdlib s =
  Option.value ~default:s (String.chop_prefix s ~prefix:"Stdlib.")

let name_of e =
  match e.exp_desc with
  | Texp_ident (p, _, _) -> Some (strip_stdlib (Path.name p))
  | _ -> None

let is_perform s = String.( = ) s "perform" || String.( = ) s "perform_atp"
let is_handle s = String.( = ) s "match_with" || String.( = ) s "try_with"

(* functions that perform no operation and do not call back into the
   program *)
let total_primitives =
  String.Set.of_list
    [
      "not";
      "&&";
      "||";
      "=";
      "<>";
      "<";
      ">";
      "<=";
      ">=";
      "==";
      "!=";
      "+";
      "-";
      "*";
      "~-";
      "ignore";
      "fst";
      "snd";
      "raise";
    ]

let args_of args =
  List.filter_map args ~f:(function _, Arg a -> Some a | _, Omitted _ -> None)

let body_of_fun e =
  match e.exp_desc with
  | Texp_function (_, Tfunction_body b) -> Some b
  | _ -> None

type clause = {
  op : string;
  params : string option list;  (** the constructor's argument binders *)
  k : string option;  (** the continuation binder *)
  extra_params : bool;  (** the clause takes arguments after [k] *)
  body : expression;
}

(* The clauses (each [Some (fun k .. -> body)] case of [effc]) and the return
   clause's body of a handler record literal; [None] for any other shape. *)
let handler_of h =
  match h.exp_desc with
  | Texp_record { fields; _ } -> (
      let field name =
        Array.find_map fields ~f:(fun (l, d) ->
            if String.( = ) l.lbl_name name then
              match d with Overridden (_, e) -> Some e | Kept _ -> None
            else None)
      in
      let retc = Option.bind (field "retc") ~f:body_of_fun in
      match Option.bind (field "effc") ~f:body_of_fun with
      | Some { exp_desc = Texp_match (_, cases, _, _); _ } -> (
          let clause c =
            match (fst (split_pattern c.c_lhs), c.c_rhs.exp_desc) with
            | ( Some { pat_desc = Tpat_construct (_, cd, pats, _); _ },
                Texp_construct (_, { cstr_name = "Some"; _ }, [ f ]) ) -> (
                match f.exp_desc with
                | Texp_function (kp :: rest, Tfunction_body body) ->
                    let params =
                      List.map pats ~f:(fun p ->
                          match p.pat_desc with
                          | Tpat_var (id, _, _) -> Some (Ident.name id)
                          | _ -> None)
                    in
                    Some
                      (Some
                         {
                           op = cd.cstr_name;
                           params;
                           k = Some (Ident.name kp.fp_param);
                           extra_params = not (List.is_empty rest);
                           body;
                         })
                | _ -> None)
            | ( Some { pat_desc = Tpat_construct _; _ },
                Texp_construct (_, { cstr_name = "None"; _ }, []) ) ->
                (* no clause: the operation is not handled here *)
                Some None
            | _ -> None
          in
          match Option.all (List.map cases ~f:clause) with
          | Some cls -> Some (List.filter_opt cls, retc)
          | None -> None)
      | _ -> None)
  | _ -> None

(* [e] is [perform (Op p1 .. pn)] or [perform_atp (Op p1 .. pn)] with exactly
   the clause's binders, in order *)
let is_perform_of cl e =
  match e.exp_desc with
  | Texp_apply (f, args) -> (
      match (name_of f, args_of args) with
      | Some p, [ c ] when is_perform p -> (
          match c.exp_desc with
          | Texp_construct (_, cd, xs) ->
              String.( = ) cd.cstr_name cl.op
              && List.length xs = List.length cl.params
              && List.for_all2_exn xs cl.params ~f:(fun x p ->
                  match (name_of x, p) with
                  | Some x, Some p -> String.( = ) x p
                  | _ -> false)
          | _ -> false)
      | _ -> false)
  | _ -> false

let is_continue_k cl e ~arg =
  match e.exp_desc with
  | Texp_apply (f, args) -> (
      match (name_of f, args_of args, cl.k) with
      | Some "continue", [ k; a ], Some kn ->
          Option.equal String.( = ) (name_of k) (Some kn) && arg a
      | _ -> false)
  | _ -> false

(* the clause re-performs its operation with the same arguments and resumes
   with the answer, and does nothing else *)
let forwards cl =
  (not cl.extra_params)
  &&
  match cl.body.exp_desc with
  | Texp_let (_, [ vb ], cont) -> (
      match vb.vb_pat.pat_desc with
      | Tpat_var (r, _, _) ->
          is_perform_of cl vb.vb_expr
          && is_continue_k cl cont ~arg:(fun a ->
              Option.equal String.( = ) (name_of a) (Some (Ident.name r)))
      | _ -> false)
  | _ -> is_continue_k cl cl.body ~arg:(is_perform_of cl)

(* the operations evaluating [e] may perform without handling them, given
   estimates [env] for the recursive functions *)
let rec escape env e =
  let all es = union_list (List.map es ~f:(escape env)) in
  match e.exp_desc with
  | Texp_ident _ | Texp_constant _ | Texp_function _ -> none
  | Texp_let (_, vbs, body) ->
      union (all (List.map vbs ~f:(fun vb -> vb.vb_expr))) (escape env body)
  | Texp_sequence (a, b) -> union (escape env a) (escape env b)
  | Texp_ifthenelse (c, t, e_opt) ->
      union
        (all [ c; t ])
        (Option.value_map e_opt ~default:none ~f:(escape env))
  | Texp_tuple es -> all (List.map es ~f:snd)
  | Texp_construct (_, _, es) -> all es
  | Texp_match (s, cases, [], _) ->
      union (escape env s)
        (all
           (List.concat_map cases ~f:(fun c ->
                c.c_rhs :: Option.to_list c.c_guard)))
  | Texp_apply (f, args) -> (
      let args = args_of args in
      match name_of f with
      | Some p when is_perform p -> (
          match args with
          | [ { exp_desc = Texp_construct (_, cd, xs); _ } ] ->
              union (Ops (String.Set.singleton cd.cstr_name)) (all xs)
          | _ -> Every)
      | Some p when is_handle p -> (
          match args with
          | thunk :: arg :: h :: rest -> (
              match handler_of h with
              | None -> Every
              | Some (cls, retc) ->
                  let handled =
                    match escape_applied env thunk with
                    | Every -> Every
                    | Ops s ->
                        Ops
                          (Set.diff s
                             (String.Set.of_list
                                (List.map cls ~f:(fun cl -> cl.op))))
                  in
                  union_list
                    [
                      handled;
                      all (List.map cls ~f:(fun cl -> cl.body));
                      Option.value_map retc ~default:none ~f:(escape env);
                      all (arg :: rest);
                    ])
          | _ -> Every)
      | Some "continue" -> all args
      | Some p when Set.mem total_primitives p -> all args
      | Some p when Map.mem env p -> union (Map.find_exn env p) (all args)
      | _ -> Every)
  | _ -> Every

(* the operations calling [thunk] may perform *)
and escape_applied env thunk =
  match thunk.exp_desc with
  | Texp_function (_, Tfunction_body b) -> escape env b
  | _ -> (
      match name_of thunk with
      | Some p when Map.mem env p -> Map.find_exn env p
      | _ -> Every)

let mentions names e =
  let found = ref false in
  let open Tast_iterator in
  let it =
    {
      default_iterator with
      expr =
        (fun self e ->
          (match name_of e with
          | Some p when Set.mem names p -> found := true
          | _ -> ());
          default_iterator.expr self e);
    }
  in
  it.expr it e;
  !found

(* where a subexpression sits relative to the handlers of the definition:
   outside any handled body; directly under one handler, whose clauses are
   given; or anywhere else inside a handled body *)
type position = Outside | Under of clause list | Unsupported

let is_outside = function Outside -> true | Under _ | Unsupported -> false

exception Reject of string

(* Walk [e] and reject a reference to one of [names] whose coercion would not
   be exact (see the header). *)
let rec walk ~names ~esc pos e =
  let go = walk ~names ~esc pos in
  let deeper = function
    | Outside -> Outside
    | Under _ | Unsupported -> Unsupported
  in
  match e.exp_desc with
  | Texp_ident _ -> (
      match (name_of e, pos) with
      | Some p, Under cls when Set.mem names p ->
          let escaping op =
            match esc with Every -> true | Ops s -> Set.mem s op
          in
          List.iter cls ~f:(fun cl ->
              if escaping cl.op && not (forwards cl) then
                raise
                  (Reject
                     (sprintf
                        "a call of %s inside a handled body runs with the \
                         handlers outside the handler, which skips its clause \
                         for %s, and that clause does not forward the \
                         operation unchanged"
                        p cl.op)))
      | Some p, Unsupported when Set.mem names p ->
          raise
            (Reject
               (sprintf
                  "%s is referred to inside a handled body other than directly \
                   under one handler of its own definition"
                  p))
      | _ -> ())
  | Texp_constant _ -> ()
  | Texp_let (_, vbs, body) ->
      List.iter vbs ~f:(fun vb -> go vb.vb_expr);
      go body
  | Texp_sequence (a, b) ->
      go a;
      go b
  | Texp_ifthenelse (c, t, e_opt) ->
      go c;
      go t;
      Option.iter e_opt ~f:go
  | Texp_tuple es -> List.iter es ~f:(fun (_, e) -> go e)
  | Texp_construct (_, _, es) -> List.iter es ~f:go
  | Texp_function (_, body) -> (
      let pos' = deeper pos in
      match body with
      | Tfunction_body b -> walk ~names ~esc pos' b
      | Tfunction_cases _ ->
          if (not (is_outside pos')) && mentions names e then
            raise
              (Reject
                 "a recursive function is referred to inside a handled body \
                  under a [function] the soundness check does not read"))
  | Texp_apply (f, args) -> (
      let args = args_of args in
      match (name_of f, args) with
      | Some p, thunk :: arg :: h :: rest when is_handle p -> (
          go arg;
          List.iter rest ~f:go;
          match handler_of h with
          | None ->
              if
                mentions names thunk
                || ((not (is_outside pos)) && mentions names h)
              then
                raise
                  (Reject
                     "a handled body or handler of a recursive definition is \
                      not of the form the translation reads")
          | Some (cls, retc) -> (
              (* clauses and the return clause run outside the handler *)
              List.iter cls ~f:(fun cl -> walk ~names ~esc (deeper pos) cl.body);
              Option.iter retc ~f:(walk ~names ~esc (deeper pos));
              let pos_body =
                match pos with Outside -> Under cls | _ -> Unsupported
              in
              match thunk.exp_desc with
              | Texp_function (_, Tfunction_body b) ->
                  walk ~names ~esc pos_body b
              | _ -> walk ~names ~esc pos_body thunk))
      | _ ->
          go f;
          List.iter args ~f:go)
  | _ ->
      if (not (is_outside pos)) && mentions names e then
        raise
          (Reject
             "a recursive function is referred to inside a handled body under \
              a construct the soundness check does not read")

(* [check vbs] for the bindings of one [let rec]: [Ok ()] when every
   coercion the translation will make for them is exact, [Error reason]
   otherwise. *)
let check (vbs : value_binding list) =
  let names =
    String.Set.of_list
    @@ List.filter_map vbs ~f:(fun vb ->
        match vb.vb_pat.pat_desc with
        | Tpat_var (id, _, _) -> Some (Ident.name id)
        | _ -> None)
  in
  try
    match (vbs, Set.to_list names) with
    | _, [] -> Ok ()
    | [ vb ], [ name ] ->
        let body =
          match vb.vb_expr.exp_desc with
          | Texp_function (_, Tfunction_body b) -> Some b
          | _ -> None
        in
        let esc =
          match body with
          | None -> Every
          | Some b ->
              let rec fix est =
                let est' = escape (String.Map.singleton name est) b in
                if ops_equal est est' then est else fix (union est est')
              in
              fix none
        in
        walk ~names ~esc Outside vb.vb_expr;
        Ok ()
    | _, _ ->
        if
          List.exists vbs ~f:(fun vb ->
              try
                walk ~names ~esc:Every Outside vb.vb_expr;
                false
              with Reject _ -> true)
        then
          Error
            "a recursive function of a mutually recursive definition is called \
             inside a handled body"
        else Ok ()
  with Reject reason -> Error reason
