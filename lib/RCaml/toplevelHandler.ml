(* The meaning of a top-level computation that performs an operation no
   handler catches.

   OCaml ends such a run with an error: an uncaught exception, or
   [Effect.Unhandled] for an effect.  RCaml reads it the same way, as a
   failure: a top-level item [let p = e] whose computation may perform an
   operation or raise an exception is read as

     let p = match_with (fun () -> e) () {
       retc = (fun v -> v);
       exnc = (function C1 _ -> assert false | ...);
       effc = fun (type a) (op : a eff) -> match op with
         | Op1 _ -> Some (fun (k : (a, _) continuation) -> assert false)
         | ... }

   with one [exnc] case per constructor of the program's [exn] type and one
   [effc] case per constructor of its [eff] type.  The handler resumes
   nothing, so a run of the wrapped program takes the steps of the original
   until an operation reaches the top level, and there it fails an
   [assert]; a refinement typing of the wrapped program therefore says that
   no operation and no exception escapes (and that every other [assert]
   holds).  In the calculus of Kawamata et al. (POPL 2024), whose type
   safety theorem lets a closed well-typed computation end in a value or in
   an operation no handler catches, the wrapping turns the second outcome
   into a failed assertion.

   A clause [assert false] is typable exactly when the clause is
   unreachable, and the refinement type system can say so only through the
   operation's argument: the clause is typed under the refinement of its
   parameters, and an operation that never reaches the handler gets a
   parameter refinement that is false.  An operation with no parameter
   ([Ask : int eff], an exception [E]) gives the clause no hypothesis to be
   false, so its [assert false] would fail even when the operation is never
   performed, which would make a safe program look unsafe.  So, in a file
   that has an item to wrap, every parameterless constructor of [eff] and
   [exn] is given one [unit] parameter ([Ask : unit -> int eff], [E of
   unit]), and every use of it in an expression or a pattern gets [()] or
   [_]: the program means the same, and the clause sees whether the
   operation can reach it.  A constructor whose every parameter is a
   function (whose refinement has no predicate) is not handled: the item is
   refused.

   [wrap] is a parse-tree rewrite, applied after [EffectSyntax.desugar] and
   before the OCaml type checker.  Contract:
   - assumes: [idxs] are positions in [str] of items the caller found to
     perform an operation at the top level;
   - guarantees: with [idxs = []], [Ok str] itself; otherwise [Ok str']
     differs from [str] only at those positions, where the bound expression
     [e] is replaced by the handled one above (the pattern, the attributes
     and the location of the item are kept, so the caller can find the item
     again), and by the parameter given to parameterless [eff] and [exn]
     constructors; [str'] type-checks in OCaml whenever [str] does, and
     every interface name the handler uses is declared by the program itself
     before the item;
   - [Error why] (nothing rewritten) when an item is not a single
     non-recursive [let]; when the program does not declare, before the
     item, the [eff] variant, the [continuation] and [handler] types and the
     [match_with] external the handler is written with; when [eff] or [exn]
     is declared more than once, or a parameterless constructor of theirs
     has a namesake in another type or is named in an attribute's text
     (which this rewrite cannot change consistently); or when a constructor
     has only function parameters.  The caller then refuses the program as
     before.

   An exception of OCaml's built-in [exn] type has no constructor list to
   enumerate; a program that declares no [exn] type of its own gets
   [exnc = Stdlib.raise], which the translation reads as "no exception
   clause", so a raise of a built-in exception still escapes and the item
   stays impure (and refused). *)

open Parsetree

(* RCaml's [toplevel_effects] setting: [Refuse] gives a program with an
   impure top-level item no meaning (it is refused); [Fail_on_escape] reads
   it as described above. *)
type toplevel_effects = Refuse | Fail_on_escape [@@deriving yojson]

(* the last declaration of a type named [name] among [items] *)
let last_type_decl name items =
  List.fold_left
    (fun acc si ->
      match si.pstr_desc with
      | Pstr_type (_, decls) -> (
          match List.find_opt (fun d -> d.ptype_name.txt = name) decls with
          | Some d -> Some d
          | None -> acc)
      | _ -> acc)
    None items

let declares_value name items =
  List.exists
    (fun si ->
      match si.pstr_desc with
      | Pstr_primitive vd -> vd.pval_name.txt = name
      | Pstr_value (_, vbs) ->
          List.exists
            (fun vb ->
              match vb.pvb_pat.ppat_desc with
              | Ppat_var { txt; _ } -> txt = name
              | _ -> false)
            vbs
      | _ -> false)
    items

(* a pattern [C] or [C _] matching every value built by constructor [cd] *)
let constructor_pattern (cd : constructor_declaration) =
  match cd.pcd_args with
  | Pcstr_tuple [] -> cd.pcd_name.txt
  | Pcstr_tuple _ | Pcstr_record _ -> cd.pcd_name.txt ^ " _"

let constructors_of name items =
  match last_type_decl name items with
  | Some { ptype_kind = Ptype_variant (_ :: _ as cds); _ } -> Some cds
  | Some _ | None -> None

(* the names the handler binds; the [toplevel_] prefix keeps them apart from
   the program's own, which the handler's clauses do not mention anyway *)
let body_placeholder = "toplevel_handled_body"

let handler_text ~exn_cds ~eff_cds =
  let exnc =
    match exn_cds with
    | None -> "Stdlib.raise"
    | Some cds ->
        "(function "
        ^ String.concat " | "
            (List.map
               (fun cd -> constructor_pattern cd ^ " -> assert false")
               cds)
        ^ ")"
  in
  let effc =
    "fun (type toplevel_op_result) (toplevel_op : toplevel_op_result eff) -> \
     match toplevel_op with "
    ^ String.concat " | "
        (List.map
           (fun cd ->
             constructor_pattern cd
             ^ " -> Some (fun (toplevel_k : (toplevel_op_result, _) \
                continuation) -> assert false)")
           eff_cds)
  in
  Printf.sprintf
    "match_with (fun () -> %s) () ({ retc = (fun toplevel_v -> toplevel_v); \
     exnc = %s; effc = %s } : (_, _) handler)"
    body_placeholder exnc effc

(* replace the placeholder identifier by [body] *)
let plug body (e : expression) =
  let open Ast_mapper in
  let mapper =
    {
      default_mapper with
      expr =
        (fun m e ->
          match e.pexp_desc with
          | Pexp_ident { txt = Longident.Lident s; _ } when s = body_placeholder
            ->
              body
          | _ -> default_mapper.expr m e);
    }
  in
  mapper.expr mapper e

let wrap_item ~before si =
  match si.pstr_desc with
  | Pstr_value (Asttypes.Nonrecursive, [ vb ]) -> (
      let missing =
        List.filter_map
          (fun (what, ok) -> if ok then None else Some what)
          [
            ("a variant type eff", constructors_of "eff" before <> None);
            ("a type continuation", last_type_decl "continuation" before <> None);
            ("a type handler", last_type_decl "handler" before <> None);
            ("match_with", declares_value "match_with" before);
          ]
      in
      match missing with
      | _ :: _ ->
          Error
            ("the program declares no effect interface to handle it with \
              (missing before the item: " ^ String.concat ", " missing ^ ")")
      | [] ->
          let eff_cds = Option.get (constructors_of "eff" before) in
          let exn_cds = constructors_of "exn" before in
          let handled =
            plug vb.pvb_expr
              (Parse.expression
                 (Lexing.from_string (handler_text ~exn_cds ~eff_cds)))
          in
          let handled = { handled with pexp_loc = vb.pvb_expr.pexp_loc } in
          Ok
            {
              si with
              pstr_desc =
                Pstr_value
                  (Asttypes.Nonrecursive, [ { vb with pvb_expr = handled } ]);
            })
  | Pstr_value (Asttypes.Recursive, _) -> Error "it is a recursive binding"
  | Pstr_value (_, _) -> Error "it binds several definitions with [and]"
  | _ -> Error "it is not a [let] item"

let type_decls name str =
  List.concat_map
    (fun si ->
      match si.pstr_desc with
      | Pstr_type (_, decls) ->
          List.filter (fun d -> d.ptype_name.txt = name) decls
      | _ -> [])
    str

(* Does [text] contain [word] delimited by non-identifier characters? *)
let mentions_word text word =
  let is_id c =
    match c with
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
    | _ -> false
  in
  let n = String.length text and m = String.length word in
  let rec at i =
    i + m <= n
    && (String.sub text i m = word
        && (i = 0 || not (is_id text.[i - 1]))
        && (i + m = n || not (is_id text.[i + m]))
       || at (i + 1))
  in
  m > 0 && at 0

(* the string constants of every attribute in [str] *)
let attribute_texts str =
  let texts = ref [] in
  let open Ast_iterator in
  let it =
    {
      default_iterator with
      attribute =
        (fun it a ->
          (match a.attr_payload with
          | PStr items ->
              List.iter
                (fun si ->
                  match si.pstr_desc with
                  | Pstr_eval ({ pexp_desc = Pexp_constant c; _ }, _) -> (
                      match c.pconst_desc with
                      | Pconst_string (t, _, _) -> texts := t :: !texts
                      | _ -> ())
                  | _ -> ())
                items
          | _ -> ());
          default_iterator.attribute it a);
    }
  in
  it.structure it str;
  !texts

(* Give each parameterless constructor of [eff] and [exn] one [unit]
   parameter, and each use of it [()] (expression) or [_] (pattern). *)
let lift_nullary (str : structure) : (structure, string) result =
  let ( let* ) = Result.bind in
  let* nullary =
    List.fold_left
      (fun acc name ->
        let* acc = acc in
        match type_decls name str with
        | [] -> Ok acc
        | [ { ptype_kind = Ptype_variant cds; _ } ] ->
            Ok
              (acc
              @ List.filter_map
                  (fun cd ->
                    match cd.pcd_args with
                    | Pcstr_tuple [] -> Some cd.pcd_name.txt
                    | _ -> None)
                  cds)
        | [ _ ] -> Ok acc
        | _ ->
            Error (Printf.sprintf "the type %s is declared more than once" name))
      (Ok []) [ "eff"; "exn" ]
  in
  let others =
    List.concat_map
      (fun si ->
        match si.pstr_desc with
        | Pstr_type (_, decls) ->
            List.concat_map
              (fun d ->
                match d.ptype_kind with
                | Ptype_variant cds
                  when not (List.mem d.ptype_name.txt [ "eff"; "exn" ]) ->
                    List.map (fun cd -> cd.pcd_name.txt) cds
                | _ -> [])
              decls
        | _ -> [])
      str
  in
  let texts = attribute_texts str in
  match
    List.find_opt
      (fun c ->
        List.mem c others || List.exists (fun t -> mentions_word t c) texts)
      nullary
  with
  | Some c ->
      Error
        (Printf.sprintf
           "the operation %s has no parameter, and it has a namesake in \
            another type or is named in an attribute's text"
           c)
  | None when nullary = [] -> Ok str
  | None ->
      let is_lifted (lid : Longident.t Location.loc) =
        match lid.txt with
        | Longident.Lident c -> List.mem c nullary
        | _ -> false
      in
      let open Ast_mapper in
      let loc = Location.none in
      let unit_ty =
        Ast_helper.Typ.constr ~loc
          (Location.mkloc (Longident.Lident "unit") loc)
          []
      in
      let mapper =
        {
          default_mapper with
          type_declaration =
            (fun m d ->
              let d =
                match d.ptype_kind with
                | Ptype_variant cds
                  when List.mem d.ptype_name.txt [ "eff"; "exn" ] ->
                    {
                      d with
                      ptype_kind =
                        Ptype_variant
                          (List.map
                             (fun cd ->
                               match cd.pcd_args with
                               | Pcstr_tuple [] ->
                                   {
                                     cd with
                                     pcd_args = Pcstr_tuple [ unit_ty ];
                                   }
                               | _ -> cd)
                             cds);
                    }
                | _ -> d
              in
              default_mapper.type_declaration m d);
          expr =
            (fun m e ->
              match e.pexp_desc with
              | Pexp_construct (lid, None) when is_lifted lid ->
                  {
                    e with
                    pexp_desc =
                      Pexp_construct
                        ( lid,
                          Some
                            (Ast_helper.Exp.construct ~loc:e.pexp_loc
                               (Location.mkloc (Longident.Lident "()")
                                  e.pexp_loc)
                               None) );
                  }
              | _ -> default_mapper.expr m e);
          pat =
            (fun m p ->
              match p.ppat_desc with
              | Ppat_construct (lid, None) when is_lifted lid ->
                  {
                    p with
                    ppat_desc =
                      Ppat_construct
                        (lid, Some ([], Ast_helper.Pat.any ~loc:p.ppat_loc ()));
                  }
              | _ -> default_mapper.pat m p);
        }
      in
      Ok (mapper.structure mapper str)

(* a constructor every parameter of which is a function *)
let only_function_params (cd : constructor_declaration) =
  match cd.pcd_args with
  | Pcstr_tuple (_ :: _ as tys) ->
      List.for_all
        (fun (ty : core_type) ->
          match ty.ptyp_desc with Ptyp_arrow _ -> true | _ -> false)
        tys
  | _ -> false

let wrap (idxs : int list) (str : structure) : (structure, string) result =
  if idxs = [] then Ok str
  else
    match lift_nullary str with
    | Error _ as e -> e
    | Ok str -> (
        match
          List.find_opt only_function_params
            (Option.value ~default:[] (constructors_of "eff" str)
            @ Option.value ~default:[] (constructors_of "exn" str))
        with
        | Some cd ->
            Error
              (Printf.sprintf
                 "the operation %s has only function parameters, whose \
                  refinement cannot say that it is never performed"
                 cd.pcd_name.txt)
        | None ->
            let rec go i before = function
              | [] -> Ok (List.rev before)
              | si :: rest ->
                  if List.mem i idxs then
                    match wrap_item ~before:(List.rev before) si with
                    | Ok si' -> go (i + 1) (si' :: before) rest
                    | Error _ as e -> e
                  else go (i + 1) (si :: before) rest
            in
            go 0 [] str)
