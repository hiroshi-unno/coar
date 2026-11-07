(* Back end B1: a CPS image of an effectful program as a higher-order
   recursion scheme (an RSFD for HorSat2/TRecS), whose tree is the program's
   effect tree (Sekiyama and Unno, OOPSLA 2024, Theorem 2: the effect tree of
   the CPS image under the top-level clauses equals the source's).

   Three steps:
   - the top level ([of_program]): pure items become nonterminals [TL_x]
     over the results of the impure items before them; impure items run in
     order, each under the top-level clauses [v_i = lam x, k. op_i(x; y. k y)]
     (nonterminals [TopOp], a terminal [opOp] with the parameter and one
     child per value of the operation's result sort) and continue with the
     next item's nonterminal; Boolean primitives are the nonterminals
     [Not], [And], [Or], [Imply], [Iff] with the handler slots;
   - lambda lifting ([lift]): each dynamic abstraction [TLam (hint, captured,
     params, body)] becomes a nonterminal named [hint<n>] with parameters
     [captured @ params], replaced by that nonterminal applied to [captured];
   - checks: [check_sorts] infers simple sorts (ground [o] and arrows) for
     every nonterminal and requires every terminal to be first order, which is
     what HorSat2 accepts; [canonical] prints a scheme up to the renaming of
     generated nonterminals and of parameters, for comparing two generators.

   Contract of [of_program]: on a program the scheme translates, the result
   is closed (every variable is a parameter of its rule) and its first rule is
   the start symbol; the [enum_values] of a result sort is complete for
   unit, Booleans and tuples of them, and any other sort is refused (where
   today's generator silently uses one [unit] child). *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld
open CpsLang

exception Refused of string

let refuse fmt = ksprintf (fun s -> raise (Refused s)) fmt
let mk_tuple ts = tapps (TTerm ("tuple" ^ string_of_int (List.length ts))) ts

let rec enum_values ~complete s =
  if Datatype.is_unit_sort s then [ TTerm "unit" ]
  else
    match s with
    | T_bool.SBool -> [ TTerm "tt"; TTerm "ff" ]
    | T_tuple.STuple sorts ->
        Common.Util.Vector.product mk_tuple
        @@ List.map sorts ~f:(enum_values ~complete)
    | _ ->
        if complete then
          refuse
            "[hors] the result sort %s of an escaping operation is not finite"
            (Term.str_of_sort s)
        else [ TTerm "unit" ]

(* the top-level clause of each operation slot, as today's generator builds
   it: the operation's CPS sort (its calling convention) is read from the
   item's solved signature, else from the [eff] declaration; the node's
   children enumerate the result sort the [eff] GADT declares for the
   operation ([op_results]), else the one in the CPS sort.  The declared
   result is used because the node's arity must be the rank the
   specification's alphabet gives the operation: the solved signature of an
   operation polymorphic in its result holds the instance this program
   performs it at, and enumerating that instance gave a node more children
   than its rank (an ill-sorted scheme).  An operation reaching the top level
   is never resumed, so the children stand for no behaviour of the program. *)
let top_handlers ~complete ?(op_results = []) eff_ops (o : Sort.o) =
  let map = match o with Sort.OpSig (map, _) -> map | _ -> [] in
  let ops = match eff_ops with Some ops -> ops | None -> map in
  List.map ops ~f:(fun (op, sort) ->
      let sort =
        Option.value ~default:sort (List.Assoc.find map op ~equal:String.equal)
      in
      let nt = Ident.Tvar ("Top" ^ String.capitalize op) in
      let t = TTerm ("op" ^ String.capitalize op) in
      let k = Ident.Tvar "k" in
      let ps n = List.init n ~f:(fun i -> Ident.Tvar ("p" ^ string_of_int i)) in
      let enum_values ~complete s =
        try enum_values ~complete s
        with Refused m ->
          refuse "%s (operation %s, %s sort %s)" m op
            (if List.Assoc.mem map op ~equal:String.equal then "solved"
             else "declared")
            (Term.str_of_sort sort)
      in
      let s_result s_arity =
        match List.Assoc.find op_results op ~equal:String.equal with
        | Some s -> s
        | None -> s_arity
      in
      let children s_arity ps =
        List.map (enum_values ~complete (s_result s_arity)) ~f:(fun v ->
            tapps (TVar k) (v :: List.map ps ~f:tvar))
      in
      let rule =
        match Sort.args_ret_of sort with
        | Sort.SArrow (s_arity, _) :: sargs, _ ->
            let ps = ps (List.length sargs) in
            (k :: ps, tapps t (children s_arity ps))
        | _s_param :: Sort.SArrow (s_arity, _) :: sargs, _ ->
            let x = Ident.Tvar "x" in
            let ps = ps (List.length sargs) in
            (x :: k :: ps, tapps t (TVar x :: children s_arity ps))
        | [], s_arity ->
            (* an ATP operation without a parameter *)
            ( [ k ],
              tapps t
                (List.map (enum_values ~complete (s_result s_arity))
                   ~f:(fun v -> TApp (TVar k, v))) )
        | _ ->
            refuse "[hors] top-level clause for %s : %s" op
              (Term.str_of_sort sort)
      in
      ((op, TNt nt), (nt, rule)))

(* the Boolean primitives, each taking the handler slots and a continuation *)
let boolean_rules n_slots =
  let x = Ident.Tvar "x" and y = Ident.Tvar "y" and k = Ident.Tvar "k" in
  let hs =
    List.init n_slots ~f:(fun i -> Ident.Tvar ("h" ^ string_of_int (i + 1)))
  in
  let un name body =
    (Ident.Tvar name, (([ x ] @ hs) @ [ k ], TApp (TVar k, body)))
  in
  let bin name body =
    (Ident.Tvar name, (([ x; y ] @ hs) @ [ k ], TApp (TVar k, body)))
  in
  let pair n p t =
    [
      un n (TApp (TNt (Ident.Tvar p), TVar x));
      bin p (tapps (TTerm t) [ TVar x; TVar y ]);
    ]
  in
  [ un "Not" (TApp (TTerm "not", TVar x)) ]
  @ pair "And" "AndP" "and" @ pair "Or" "OrP" "or"
  @ pair "Imply" "ImplyP" "imply"
  @ pair "Iff" "IffP" "iff"

(* [lift rules]: lambda lifting of target rules into an RSFD *)
let lift ~taken (rules : (tvar * (tvar list * tterm)) list) : HOMC.RSFD.t =
  let out = ref [] in
  let rec go = function
    | TVar x -> HOMC.RSFD.Var x
    | TNt n -> HOMC.RSFD.Nonterm n
    | TTerm t -> HOMC.RSFD.Term (Ident.Tvar t)
    | TApp (t1, t2) -> HOMC.RSFD.App (go t1, go t2)
    | TLam (hint, captured, params, body) ->
        let nt = Ident.mk_fresh_tvar_avoiding ~prefix:hint ~taken () in
        let body = go body in
        out := (nt, (captured @ params, body)) :: !out;
        HOMC.RSFD.apps (HOMC.RSFD.Nonterm nt)
          (List.map captured ~f:(fun x -> HOMC.RSFD.Var x))
  in
  let top = List.map rules ~f:(fun (nt, (ps, t)) -> (nt, (ps, go t))) in
  top @ List.rev !out

type options = { eta_mode : SchemeO24.eta_mode; complete_enum : bool }

let legacy_options =
  { eta_mode = SchemeO24.Legacy_guess; complete_enum = false }

module T = CpsScheme.Traverse (SchemeO24)

(* [of_program ~options prog n]: the recursion scheme of the first [n] items
   of [prog] under scheme O24 *)
let of_program ?(options = legacy_options) (prog : program) n_items :
    (HOMC.RSFD.t, string) Result.t =
  try
    let prog_vars = vars_program prog in
    let taken v = Set.mem prog_vars v in
    let items = List.take prog.items n_items in
    let tl_first = Ident.mk_fresh_tvar_avoiding ~prefix:"TL" ~taken () in
    let st0 =
      SchemeO24.
        {
          scope = [];
          ntenv = Map.Poly.empty;
          taken;
          eff_ops = prog.eff_ops;
          eta_mode = options.eta_mode;
        }
    in
    let _, tl_nt, tl_args, tl_rules, rules, top_nts =
      List.fold items ~init:(Map.Poly.empty, tl_first, [], [], [], [])
        ~f:(fun (ntenv, tl_nt, tl_args, tl_rules, rules, top_nts) it ->
          let st = { st0 with scope = tl_args; ntenv } in
          if it.is_pure then
            let nt = Ident.Tvar ("TL_" ^ Ident.name_of_tvar it.name) in
            let self = tapps (TNt nt) (List.map tl_args ~f:tvar) in
            let ntenv_body =
              if it.is_rec then Map.Poly.set ntenv ~key:it.name ~data:self
              else ntenv
            in
            let v =
              match it.body.desc with
              | Return v -> T.value { st with ntenv = ntenv_body } v
              | _ -> refuse "[hors] a pure item that is not a value"
            in
            ( Map.Poly.set ntenv ~key:it.name ~data:self,
              tl_nt,
              tl_args,
              tl_rules,
              rules @ [ (nt, (tl_args, v)) ],
              top_nts )
          else
            let tl_nt' = Ident.mk_fresh_tvar_avoiding ~prefix:"TL" ~taken () in
            let hs, top_rules =
              List.unzip
              @@ top_handlers ~complete:options.complete_enum
                   ~op_results:prog.op_results prog.eff_ops
                   it.body.ty.op_sig
            in
            let st =
              if it.is_rec then
                refuse "[hors] a recursive impure top-level item"
              else st
            in
            let t =
              match
                T.comp st it.body
                  { hs; k = tapps (TNt tl_nt') (List.map tl_args ~f:tvar) }
              with
              | t, [] -> t
              | _ -> refuse "[hors] eta parameters at the top level"
            in
            let new_tops =
              List.filter top_rules ~f:(fun (nt, _) ->
                  not (List.mem top_nts nt ~equal:Ident.tvar_equal))
            in
            ( ntenv,
              tl_nt',
              tl_args @ [ it.name ],
              tl_rules @ [ (tl_nt, (tl_args, t)) ] @ new_tops,
              rules,
              top_nts @ List.map new_tops ~f:fst ))
    in
    ignore top_nts;
    let n_slots =
      match prog.eff_ops with Some ops -> List.length ops | None -> 0
    in
    let taken v =
      taken v
      || List.exists (tl_rules @ rules) ~f:(fun (nt, _) ->
          Ident.tvar_equal nt v)
    in
    Ok
      (lift ~taken
         (tl_rules
         @ [ (tl_nt, (tl_args, TTerm "unit")) ]
         @ rules @ boolean_rules n_slots))
  with
  | Refused msg | SchemeO24.Refused msg -> Error msg
  | Failure msg -> Error ("[hors] " ^ msg)

(** {2 Checks} *)

(* [canonical rules]: the rules reachable from the first, in depth-first
   order, generated nonterminals (a name ending in a digit) renamed [N<i>] in
   order of first reference and parameters renamed by position; then the
   rules not reached, by name, with generated names shown as [dead].
   Contract: two schemes that differ only by such renamings (and by the order
   of their rules after the first) have equal images. *)
let canonical (rules : HOMC.RSFD.t) =
  let generated nt =
    let s = Ident.name_of_tvar nt in
    String.length s > 0 && Char.is_digit s.[String.length s - 1]
  in
  let table = Hashtbl.Poly.create () in
  List.iter rules ~f:(fun (nt, r) -> Hashtbl.Poly.set table ~key:nt ~data:r);
  let names = Hashtbl.Poly.create () in
  let counter = ref 0 in
  let name_of nt =
    if not (generated nt) then Ident.name_of_tvar nt
    else
      match Hashtbl.Poly.find names nt with
      | Some n -> n
      | None ->
          let n = sprintf "N%d" !counter in
          incr counter;
          Hashtbl.Poly.set names ~key:nt ~data:n;
          n
  in
  let visited = Hash_set.Poly.create () in
  let out = ref [] in
  let rec nts acc = function
    | HOMC.RSFD.Nonterm n -> n :: acc
    | App (t1, t2) -> nts (nts acc t1) t2
    | _ -> acc
  in
  let print_rule nt (ps, body) =
    let idx = List.mapi ps ~f:(fun i p -> (p, sprintf "v%d" i)) in
    let rec pr = function
      | HOMC.RSFD.Var x -> (
          match List.Assoc.find idx x ~equal:Ident.tvar_equal with
          | Some v -> v
          | None -> "?free:" ^ Ident.name_of_tvar x)
      | Nonterm n -> name_of n
      | Term t -> (
          (* today's generator writes the parameters of its Boolean rules as
             terminals; a terminal spelled as a parameter is that parameter *)
          match List.Assoc.find idx t ~equal:Ident.tvar_equal with
          | Some v -> v
          | None -> Ident.name_of_tvar t)
      | App (t1, t2) -> sprintf "(%s %s)" (pr t1) (pr t2)
      | _ -> "?case"
    in
    sprintf "%s/%d -> %s" (name_of nt) (List.length ps) (pr body)
  in
  let rec visit nt =
    if not (Hash_set.mem visited nt) then (
      Hash_set.add visited nt;
      ignore (name_of nt);
      match Hashtbl.Poly.find table nt with
      | None -> out := sprintf "%s undefined" (name_of nt) :: !out
      | Some ((_, body) as r) ->
          out := print_rule nt r :: !out;
          List.iter (List.rev (nts [] body)) ~f:visit)
  in
  (match rules with (nt, _) :: _ -> visit nt | [] -> ());
  let reached = List.rev !out in
  let dead =
    List.filter_map rules ~f:(fun (nt, r) ->
        if Hash_set.mem visited nt then None
        else if generated nt then Some (sprintf "dead/%d" (List.length (fst r)))
        else Some (print_rule nt r))
    |> List.sort ~compare:String.compare
  in
  reached @ dead

(* [check_sorts rules]: simple-sort inference.  [Ok n] with the number of
   rules when every nonterminal has one sort, the start symbol (the first
   rule) is ground and every terminal is used first order (its arguments
   ground); [Error] names the first clash.  A rule body may be of function
   sort, which HorSat2 reads. *)
let check_sorts (rules : HOMC.RSFD.t) =
  let module U = struct
    type s = O | Arr of s * s | V of s option ref
  end in
  let open U in
  let rec repr = function V { contents = Some s } -> repr s | s -> s in
  let rec occurs r s =
    match repr s with
    | V r' -> phys_equal r r'
    | Arr (a, b) -> occurs r a || occurs r b
    | O -> false
  in
  let rec unify a b =
    match (repr a, repr b) with
    | O, O -> ()
    | V r1, V r2 when phys_equal r1 r2 -> ()
    | V r, s | s, V r ->
        if occurs r s then failwith "cyclic sort" else r := Some s
    | Arr (a1, b1), Arr (a2, b2) ->
        unify a1 a2;
        unify b1 b2
    | _ -> failwith "sort clash"
  in
  let fresh () = V (ref None) in
  let nt_sorts = Hashtbl.Poly.create () in
  let sort_of_nt n = Hashtbl.Poly.find_or_add nt_sorts n ~default:fresh in
  let term_sorts = Hashtbl.Poly.create () in
  try
    List.iter rules ~f:(fun (nt, (ps, body)) ->
        let penv = List.map ps ~f:(fun p -> (p, fresh ())) in
        let rec infer = function
          | HOMC.RSFD.Var x -> (
              match List.Assoc.find penv x ~equal:Ident.tvar_equal with
              | Some s -> s
              | None -> failwith ("free variable " ^ Ident.name_of_tvar x))
          | Nonterm n -> sort_of_nt n
          | Term t when List.Assoc.mem penv t ~equal:Ident.tvar_equal ->
              List.Assoc.find_exn penv t ~equal:Ident.tvar_equal
          | Term t ->
              let s = fresh () in
              Hashtbl.Poly.add_multi term_sorts ~key:t ~data:s;
              s
          | App (t1, t2) ->
              let r = fresh () in
              (try unify (infer t1) (Arr (infer t2, r))
               with Failure m ->
                 failwith (sprintf "%s in rule %s" m (Ident.name_of_tvar nt)));
              r
          | _ -> failwith "case"
        in
        (* a body may be of function sort (HorSat2 reads such rules); the
           start symbol's is ground, checked below *)
        let s_body = infer body in
        let s =
          List.fold_right penv ~init:s_body ~f:(fun (_, s) acc -> Arr (s, acc))
        in
        try unify (sort_of_nt nt) s
        with Failure m ->
          failwith (sprintf "%s at nonterminal %s" m (Ident.name_of_tvar nt)));
    (match rules with
    | (start, _) :: _ -> (
        try unify (sort_of_nt start) O
        with Failure m ->
          failwith (sprintf "%s: the start symbol is not ground" m))
    | [] -> ());
    (* every terminal first order *)
    let rec first_order s =
      match repr s with
      | O -> true
      | V r ->
          r := Some O;
          true
      | Arr (a, b) -> (
          (match repr a with V r -> r := Some O | _ -> ());
          match repr a with O -> first_order b | _ -> false)
    in
    Hashtbl.Poly.iteri term_sorts ~f:(fun ~key ~data ->
        List.iter data ~f:(fun s ->
            if not (first_order s) then
              failwith
                ("terminal " ^ Ident.name_of_tvar key
               ^ " used at a higher-order sort")));
    Ok (List.length rules)
  with Failure m -> Error m
