(** Deciding the integer atoms of a validity question that its own integer
    facts decide.

    [decide ~entails phi] takes a validity question [phi] (a formula in
    negation normal form is not required) and returns a formula equivalent to
    it in every model.  Let [D] be the top-level disjuncts of [phi] that are
    integer literals free of bit-vectors (a comparison or an equation of two
    integer terms, possibly negated), and [L] the conjunction of their
    negations: the facts that hold wherever [phi]'s other disjuncts have to
    carry it.  An integer atom [a] occurring anywhere else in [phi] (also in a
    guard of an [ite] term), whose variables no binder of [phi] binds, is
    replaced by [true] where [entails L a] says [L] implies [a], and by [false]
    where it says [L] implies [not a]; the result is simplified and the step
    repeated while it decides something, at most [rounds] times.

    Why it is exact: [phi] is [D \/ R].  Where some disjunct of [D] is true,
    [phi] and the rewrite are both true (the rewrite keeps [D], since an atom
    of [D] is not replaced -- it is a fact, not a candidate).  Where every
    disjunct of [D] is false, [L] holds, so each replaced atom has the value
    it is replaced by, and [R] and its rewrite agree.  [entails] must answer
    [true] only for a valid implication; any other answer leaves the atom.

    What it buys: a question that couples integer facts with words read
    through [int_to_bv] ([forall q. q < len => w[q] = 2^64 - 1] instantiated
    at the word index [i div 64]) leaves the solver a case split on the
    instance's guard ([0 <= i div 64 < len]) that its integer reasoning closes
    at once alone and Z3 5.1.0 does not close beside the conversion: four
    variables, [64 k + r >= 0 /\ 0 <= r < 64 /\ (k >= 0 => w = 2^64 - 1)] and
    bit 5 of [int_to_bv 64 w] clear, run out of 15 s, and are refuted at once
    with [k >= 0] stated.  The facts that decide the guard are already in the
    question; this asks the integer half for them alone. *)
open Core
open Ast.LogicOld

let rec bv_free_int_term t =
  (match Term.sort_of t with
  | s -> not (Term.is_bv_sort s))
  &&
  match t with
  | Term.Var _ -> true
  | Term.FunApp (T_bool.Formula _, _, _) -> false
  | Term.FunApp (T_bool.IfThenElse, _, _) -> false
  | Term.FunApp (_, args, _) -> List.for_all args ~f:bv_free_int_term
  | Term.LetTerm _ -> false

(** whether [atom] compares two integer terms free of bit-vectors, embedded
    formulas and [ite] *)
let is_int_atom = function
  | Atom.App
      ( Predicate.Psym
          ( T_int.Leq | T_int.Geq | T_int.Lt | T_int.Gt | T_bool.Eq
          | T_bool.Neq ),
        [ t1; t2 ],
        _ ) -> (
      try
        Term.is_int_sort (Term.sort_of t1)
        && bv_free_int_term t1 && bv_free_int_term t2
      with _ -> false)
  | _ -> false

(* the atom of an integer literal, with its sign *)
let int_literal = function
  | Formula.Atom (a, _) when is_int_atom a -> Some (a, true)
  | Formula.UnaryOp (Formula.Not, Formula.Atom (a, _), _) when is_int_atom a ->
      Some (a, false)
  | _ -> None

(* every variable a binder of [phi] binds, also inside embedded formulas *)
let bound_names phi =
  Set.Poly.map ~f:fst (Formula.quantified_sort_env_of phi)

let decide ?(rounds = 3) ~entails phi =
  let equal_atom a b = Stdlib.( = ) a b in
  let round phi =
    let disjuncts = Formula.disjuncts_list_of phi in
    let facts, rest =
      List.partition_map disjuncts ~f:(fun d ->
          match int_literal d with
          | Some (a, pos) -> First (d, a, pos)
          | None -> Second d)
    in
    if List.is_empty facts || List.is_empty rest then None
    else
      let fact_atoms = List.map facts ~f:(fun (_, a, _) -> a) in
      let l =
        Formula.and_of
          (List.map facts ~f:(fun (d, _, _) -> Formula.negate d))
      in
      let bound = bound_names phi in
      (* an atom one of whose variables the facts do not mention is implied
         by them, or refuted, only if it is valid or unsatisfiable by itself,
         which a simplified question does not hold; it is not asked about *)
      let fact_vars = Formula.tvs_of l in
      (* the candidate atoms of [rest], in order of first occurrence *)
      let candidates = ref [] in
      let rec visit_atom a =
        (if is_int_atom a
            && (not (List.mem fact_atoms a ~equal:equal_atom))
            && (not (List.mem !candidates a ~equal:equal_atom))
            && Set.is_empty (Set.inter (Atom.tvs_of a) bound)
            && Set.is_subset (Atom.tvs_of a) ~of_:fact_vars
         then candidates := a :: !candidates);
        match a with
        | Atom.App (_, args, _) -> List.iter args ~f:visit_term
        | _ -> ()
      and visit_term t =
        Term.iter_atom t ~f:(fun a -> visit_atom a)
      in
      List.iter rest ~f:(fun d ->
          ignore
          @@ Formula.map_atom d ~f:(fun a ->
                 visit_atom a;
                 Formula.mk_atom a));
      let decided =
        List.filter_map (List.rev !candidates) ~f:(fun a ->
            let pa = Formula.mk_atom a in
            if entails l pa then Some (a, true)
            else if entails l (Formula.mk_neg pa) then Some (a, false)
            else None)
      in
      if List.is_empty decided then None
      else
        let rec on_atom a =
          match List.Assoc.find decided a ~equal:equal_atom with
          | Some true -> Formula.mk_true ()
          | Some false -> Formula.mk_false ()
          | None -> (
              match a with
              | Atom.App (p, args, info) ->
                  Formula.mk_atom
                    (Atom.mk_app ~info p
                       (List.map args ~f:(Term.map_atom ~f:on_atom)))
              | _ -> Formula.mk_atom a)
        in
        let rest' = List.map rest ~f:(Formula.map_atom ~f:on_atom) in
        Some
          (Ast.Evaluator.simplify
             (Formula.or_of (List.map facts ~f:(fun (d, _, _) -> d) @ rest')))
  in
  let rec loop n phi =
    if n <= 0 then phi
    else match round phi with None -> phi | Some phi' -> loop (n - 1) phi'
  in
  loop rounds phi
