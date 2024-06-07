(** Module for Qualifier Dependency *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

type act = int * int * pred_sym
type lit = LFormula of Formula.t * act | LTrue | LFalse

type t =
  | CAtom of lit
  | CNeg of t
  | CImply of t * t
  | CAnd of t * t
  | COr of t * t
  | CEquiv of t * t

let is_int_psym = function
  | T_int.Lt | T_int.Gt | T_int.Geq | T_int.Leq | T_bool.Eq | T_bool.Neq -> true
  | _ -> false

let mk_act a b psym =
  assert (is_int_psym psym);
  (a, b, psym)

let mk_lit_formula phi act = LFormula (phi, act)
let mk_atom lit = CAtom lit
let mk_neg t = CNeg t
let mk_imply t1 t2 = CImply (t1, t2)
let mk_and t1 t2 = CAnd (t1, t2)
let mk_or t1 t2 = COr (t1, t2)

let and_of ts =
  let rec aux acc = function
    | [] -> acc
    | CAtom LTrue :: ts -> aux acc ts
    | CAtom LFalse :: _ -> CAtom LFalse
    | t :: ts -> aux (mk_and acc t) ts
  in
  match ts with [] -> CAtom LTrue | x :: xs -> aux x xs

let or_of ts =
  let rec aux acc = function
    | [] -> acc
    | CAtom LTrue :: _ -> CAtom LTrue
    | CAtom LFalse :: ts -> aux acc ts
    | t :: ts -> aux (mk_or acc t) ts
  in
  match ts with [] -> CAtom LFalse | x :: xs -> aux x xs

let mk_equiv t1 t2 = CEquiv (t1, t2)

(* let rec and_of ts = if List *)
let lformula_from_atom atm = mk_lit_formula @@ Formula.mk_atom atm

let str_of_act (a, b, psym) =
  let a = if a = 0 then "" else if a = 1 then "_" else sprintf "%d * _" a in
  let b = if b = 0 then "" else sprintf "+ %d" b in
  sprintf "%s %s %s 0" a b (Predicate.str_of_psym psym)

let str_of_lit = function
  | LFormula (phi, act) -> sprintf "%s:%s" (Formula.str_of phi) (str_of_act act)
  | LTrue -> "true"
  | LFalse -> "false"

let rec str_of = function
  | CAtom lit -> sprintf "%s" (str_of_lit lit)
  | CNeg t -> sprintf "!%s" @@ String.paren @@ str_of t
  | CImply (t1, t2) ->
      sprintf "%s => %s" (String.paren @@ str_of t1) (String.paren @@ str_of t2)
  | CAnd (t1, t2) ->
      sprintf "%s /\\ %s" (String.paren @@ str_of t1) (String.paren @@ str_of t2)
  | COr (t1, t2) ->
      sprintf "%s \\/ %s" (String.paren @@ str_of t1) (String.paren @@ str_of t2)
  | CEquiv (t1, t2) ->
      sprintf "%s <=> %s" (String.paren @@ str_of t1) (String.paren @@ str_of t2)

let condition_of_lit env = function
  | LFormula (phi, (a, b, psym)) -> (
      assert (is_int_psym psym);
      match Map.Poly.find env phi with
      | Some x ->
          let var = Term.mk_var x T_int.SInt in
          let t =
            T_int.mk_add
              (T_int.mk_mult var (T_int.from_int a))
              (T_int.from_int b)
          in
          Formula.mk_atom @@ Atom.mk_psym_app psym [ t; T_int.zero () ]
      | None ->
          print_endline ("phi: " ^ Formula.str_of phi);
          print_endline
            ("env: "
            ^ String.concat_map_list ~sep:"," ~f:(fun (phi, x) ->
                  Formula.str_of phi ^ "|->" ^ Ident.name_of_tvar x)
            @@ Map.Poly.to_alist env);
          failwith "condition_of_lit")
  | LTrue -> Formula.mk_true ()
  | LFalse -> Formula.mk_false ()

let rec condition_of env = function
  | CAtom lit -> condition_of_lit env lit
  | CNeg t -> Formula.mk_neg @@ condition_of env t
  | CAnd (t1, t2) -> Formula.mk_and (condition_of env t1) (condition_of env t2)
  | COr (t1, t2) -> Formula.mk_or (condition_of env t1) (condition_of env t2)
  | CImply (t1, t2) ->
      Formula.mk_imply (condition_of env t1) (condition_of env t2)
  | CEquiv (t1, t2) ->
      Formula.mk_and
        (Formula.mk_imply (condition_of env t1) (condition_of env t2))
        (Formula.mk_imply (condition_of env t2) (condition_of env t1))

let formula_of_lit = function
  | LFormula (phi, _) -> phi
  | LTrue -> Formula.mk_true ()
  | LFalse -> Formula.mk_false ()

let rec formula_of = function
  | CAtom lit -> formula_of_lit lit
  | CNeg t -> Formula.mk_neg @@ formula_of t
  | CAnd (t1, t2) -> Formula.mk_and (formula_of t1) (formula_of t2)
  | COr (t1, t2) -> Formula.mk_or (formula_of t1) (formula_of t2)
  | CImply (t1, t2) -> Formula.mk_imply (formula_of t1) (formula_of t2)
  | CEquiv (t1, t2) ->
      Formula.mk_and
        (Formula.mk_imply (formula_of t1) (formula_of t2))
        (Formula.mk_imply (formula_of t2) (formula_of t1))

let rec map_atom ~f = function
  | CAtom lit -> f lit
  | CNeg t -> mk_neg @@ map_atom ~f t
  | CAnd (t1, t2) -> mk_and (map_atom ~f t1) (map_atom ~f t2)
  | COr (t1, t2) -> mk_or (map_atom ~f t1) (map_atom ~f t2)
  | CImply (t1, t2) -> mk_imply (map_atom ~f t1) (map_atom ~f t2)
  | CEquiv (t1, t2) ->
      mk_and
        (mk_imply (map_atom ~f t1) (map_atom ~f t2))
        (mk_imply (map_atom ~f t2) (map_atom ~f t1))

let qual_and_deps_of qual conds =
  let qual = Normalizer.normalize @@ Evaluator.simplify qual in
  let dep =
    and_of
    @@ List.dedup_and_sort ~compare:Stdlib.compare
    @@ List.map conds ~f:(fun cond ->
           let cond = Normalizer.normalize @@ Evaluator.simplify cond in
           mk_atom @@ mk_lit_formula cond (mk_act 1 0 T_int.Gt))
  in
  let dep =
    if Stdlib.(dep = CAtom LTrue) then CAtom LTrue
    else mk_imply (mk_atom @@ mk_lit_formula qual @@ mk_act 1 0 T_bool.Neq) dep
  in
  (qual, dep)
