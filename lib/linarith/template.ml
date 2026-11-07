(* Linear templates: formulas over program variables whose coefficients are
   unknowns, to be fixed by a coefficient solver ([CoeffSolver]) once their
   conditions are stated as constraints on the unknowns ([Farkas]).

   An atom over the variables [x_1 .. x_n] (all integer or all real) is
   [c_0 + c_1 x_1 + ... + c_n x_n >= 0] with fresh unknowns [c_i] of the
   variables' sort; a template of shape [(conj, disj)] is a disjunction of
   [disj] conjunctions of [conj] atoms, every atom with unknowns of its own.
   The shape is the hypothesis space: a condition with no solution at one
   shape may have one at a larger shape, and the caller decides the order
   (the template-based Horn constraint solving of Unno and Terauchi, TACAS
   2015, starts from one atom per predicate). *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* One atom: [const + sum_i coeffs_i * vars_i >= 0]. *)
type atom = {
  vars : (Ident.tvar * Sort.t) list;
  coeffs : (Ident.tvar * Sort.t) list;  (** one unknown per variable *)
  const : Ident.tvar * Sort.t;
}

(* A template: [OR_d AND_c atoms.(d).(c)]. *)
type t = atom list list

(* [atom ?unknown_sort ~prefix vars]: an atom with fresh unknowns named with
   [prefix].  Pre: [vars] all integer or all real.  The unknowns take
   [unknown_sort] when given (real unknowns over integer variables state an
   atom with rational coefficients, which a caller scales to integers), else
   the variables' sort (integer for an empty [vars]). *)
let atom ?unknown_sort ~prefix vars =
  let sort =
    match (unknown_sort, vars) with
    | Some s, _ -> s
    | None, (_, s) :: _ when Term.is_real_sort s -> T_real.SReal
    | None, _ -> T_int.SInt
  in
  let taken = ref (Set.Poly.of_list (List.map vars ~f:fst)) in
  let fresh () =
    let variable =
      Ident.mk_fresh_tvar_avoiding ~prefix
        ~taken:(fun variable -> Set.mem !taken variable) ()
    in
    taken := Set.add !taken variable;
    (variable, sort)
  in
  { vars; coeffs = List.map vars ~f:(fun _ -> fresh ()); const = fresh () }

(* [make ~prefix ~conj ~disj vars]: a template of shape [(conj, disj)]. *)
let make ~prefix ~conj ~disj vars : t =
  List.init disj ~f:(fun _ -> List.init conj ~f:(fun _ -> atom ~prefix vars))

(* The unknowns of an atom and of a template, in order. *)
let unknowns_of_atom a = a.const :: a.coeffs
let unknowns (t : t) = List.concat_map (List.concat t) ~f:unknowns_of_atom

let num_of a =
  if Term.is_real_sort (snd a.const) then Farkas.Num.real_num
  else Farkas.Num.int_num

let var (v, s) = Term.mk_var v s

(* [atom_formula a]: the atom as a formula over its variables and unknowns
   (bilinear: each term is an unknown times a variable). *)
let atom_formula a =
  let num = num_of a in
  let mul =
    if Term.is_real_sort (snd a.const) then T_real.mk_rmul else T_int.mk_mul
  in
  Formula.geq
    (num.sum
       (var a.const
       :: List.map2_exn a.coeffs a.vars ~f:(fun c x -> mul (var c) (var x))))
    (Farkas.Num.zero num)

(* [formula t]: the template as a formula over its variables and unknowns. *)
let formula (t : t) =
  Formula.or_of
    (List.map t ~f:(fun c -> Formula.and_of (List.map c ~f:atom_formula)))

(* [implied_by ~prefix rows a]: linear constraints over fresh multipliers
   (named with [prefix]) and [a]'s unknowns stating that the rows
   [k . x <= b] over [a.vars] (in order) imply the atom, by the affine form
   of Farkas' lemma: [-coeffs . x <= const] is a non-negative combination of
   the rows, weakened in its bound.
   Post: any solution makes the implication valid over the rationals (and
   over the integers).  The multipliers take the unknowns' sort; for rows
   with a rational solution, whenever some rational atom is implied the
   constraints have a solution, scaled to integers when the unknowns are
   integers (every constraint is homogeneous in the multipliers and the
   unknowns jointly).  Raises when a row is not of [a.vars]' width. *)
let implied_by ~prefix rows a =
  let width = List.length a.vars in
  if List.exists rows ~f:(fun (coeffs, _) -> List.length coeffs <> width) then
    invalid_arg "Template.implied_by: row width differs from template variables";
  let num = num_of a in
  let taken =
    Set.Poly.of_list (List.map (a.vars @ unknowns_of_atom a) ~f:fst)
  in
  let c = Farkas.combination ~num ~taken ~prefix rows in
  (Formula.leq c.bound (var a.const) :: c.nonneg)
  @ List.mapi a.coeffs ~f:(fun col ci ->
      Formula.eq (c.column col) (num.neg (var ci)))

(* [instantiate t sol]: the template with the unknowns replaced by their
   values in [sol] (an unknown [sol] does not mention stays). *)
let instantiate (t : t) sol =
  Evaluator.simplify @@ Formula.subst (Map.Poly.of_alist_exn sol) (formula t)
