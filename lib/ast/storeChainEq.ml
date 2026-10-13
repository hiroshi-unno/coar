(* Equations between a chain of writes into an array variable and another array
   term, solved for the variable.

   THE REWRITE.  Let [x] be an array variable, [c1, ..., cn] integer literals
   and [A] a term in which [x] does not occur (nor in any written value).  Write
   [C] for the set of distinct literals among the [ci] and [w_c] for the value
   written LAST at [c] (the outermost [store] at that index).  Then

     store (... store (x, c1, v1) ...) cn vn = A
       <=>  (/\_{c in C} select A c = w_c)
            /\ exists (y_c)_{c in C}. x = store_{c in C} (A, c, y_c)

   in every model and at every assignment: both sides say that the chain and
   [A] agree at each [c] (where the chain holds [w_c]) and outside [C] (where
   the chain holds [x]); the right-hand side's [y_c] stands for [x]'s own,
   unconstrained, value at [c].  So replacing a TOP-LEVEL CONJUNCT of a
   satisfiability question by the right-hand side, with the [y_c] fresh free
   variables, gives an equisatisfiable question, every model of which is a
   model of the original once the [y_c] are forgotten, and every model of the
   original extends to one of it ([y_c := x[c]]).  Not under a negation or a
   disjunction, where the fresh variables would not be existential.

   WHY.  Z3 (5.1.0) reduces an equation between arrays to extensionality, and
   when one side is a [lambda] that leaves a quantifier: on
   [store x1 2 2 = (lambda k. ite (2 <= k) (ite (k < 3) 2 11) 0)], alone or in
   a pooled context, it runs to any budget given and answers
   [unknown (incomplete quantifiers)].  The rewritten question
   [x1 = store L 2 y /\ select L 2 = 2] is answered [sat] in milliseconds,
   since an equation that defines a variable is eliminated before search.
   Such equations arise where a solver's model value of an array (a
   [lambda]) is substituted into a clause that writes into an array variable.

   [solve phis] returns the rewritten formulas and the fresh variables it
   introduced, with their sorts; [phis] itself (physically) and [] when no
   conjunct has the shape. *)

open Core
open Common.Ext
open LogicOld

let int_literal = function
  | Term.FunApp (T_int.Int n, [], _) -> Some n
  | _ -> None

(* the writes of a chain, outermost first, and the array written into; [None]
   unless every index is an integer literal and the chain ends in a variable
   below at least one write *)
let chain_of t =
  let rec go acc = function
    | Term.FunApp (T_array.AStore (si, se), [ a; i; v ], _) -> (
        match int_literal i with
        | Some n -> go ((n, i, v, si, se) :: acc) a
        | None -> None)
    | Term.Var (x, s, _) when not (List.is_empty acc) ->
        Some (x, s, List.rev acc)
    | _ -> None
  in
  go [] t

(* the rewrite of one conjunct, when it has the shape *)
let solve_eq t1 t2 =
  let try_side chain other =
    match chain_of chain with
    | None -> None
    | Some (x, xs, writes) ->
        let occurs t = Set.mem (Term.tvs_of t) x in
        if occurs other || List.exists writes ~f:(fun (_, _, v, _, _) -> occurs v)
        then None
        else
          (* outermost first, so the first write met at an index is the last
             one made there *)
          let last =
            List.fold writes ~init:[] ~f:(fun acc ((n, _, _, _, _) as w) ->
                if List.exists acc ~f:(fun (m, _, _, _, _) -> Z.equal n m) then
                  acc
                else w :: acc)
            |> List.rev
          in
          let fresh =
            List.map last ~f:(fun (_, _, _, _, se) ->
                (Ident.mk_fresh_tvar (), se))
          in
          let target =
            List.fold2_exn last fresh ~init:other
              ~f:(fun acc (_, i, _, si, se) (y, ys) ->
                T_array.mk_store si se acc i (Term.mk_var y ys))
          in
          let reads =
            List.map last ~f:(fun (_, i, w, si, se) ->
                Formula.eq (T_array.mk_select si se other i) w)
          in
          Some
            ( Formula.and_of (Formula.eq (Term.mk_var x xs) target :: reads),
              fresh )
  in
  match try_side t1 t2 with Some r -> Some r | None -> try_side t2 t1

let solve_conjunct phi =
  match phi with
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _) ->
      solve_eq t1 t2
  | _ -> None

let solve phis =
  let fresh = ref [] in
  let phis' =
    List.map phis ~f:(fun phi ->
        let changed = ref false in
        let cs' =
          List.map (Formula.conjuncts_list_of phi) ~f:(fun c ->
              match solve_conjunct c with
              | Some (c', ys) ->
                  changed := true;
                  fresh := !fresh @ ys;
                  c'
              | None -> c)
        in
        if !changed then Formula.and_of cs' else phi)
  in
  if List.is_empty !fresh then (phis, []) else (phis', !fresh)

(* [solve] after a contextual rewrite, for an equation that sits under an [ite]
   whose condition the question's own top-level literals decide.  A resolution
   question substitutes a model value into a clause whose step writes
   [ite (val = i) (store a i 0) (store a i i)]; with [i] a literal and [val] a
   variable the equation reaches the solver as
   [0 = 7 - x4 /\ true = ite (x4 = 6) (L = store x1 6 0) (L = store x1 6 6)],
   [L] a [lambda], and [solve] finds no top-level conjunct to rewrite, so Z3
   meets the lambda extensionality question [solve] exists to avoid and runs
   to its budget.  [Evaluator.elim_onepoint_and_split_binders_contextual]
   replaces an [ite] by the branch its context's linear literals entail (here
   [x4 = 7] refutes [x4 = 6]), and [Evaluator.simplify] turns [true = P] into
   [P]; both are equivalent to their input in every model, so the composition
   with [solve] keeps [solve]'s contract: an equisatisfiable question whose
   models, without the fresh variables, are the original's.  A variable the
   rewrite removes is one the question does not depend on, so a model that
   leaves it unassigned is still a model of [phis] at any value of it.

   Returns what [solve phis] returns unless the contextual form has more
   equations [solve] rewrites; then the rewritten contextual form. *)
let solve_contextual phis =
  let ((_, fresh0) as plain) = solve phis in
  let phis_c =
    List.map phis ~f:Evaluator.elim_onepoint_and_split_binders_contextual
  in
  if List.for_all2_exn phis phis_c ~f:phys_equal then plain
  else
    let ((_, fresh) as r) = solve (List.map phis_c ~f:Evaluator.simplify) in
    if List.length fresh > List.length fresh0 then r else plain
