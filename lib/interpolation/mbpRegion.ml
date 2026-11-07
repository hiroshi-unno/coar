(* A chain pair's region by model-based projection of its derivation segment.

   A counter-play is a derivation of a strategy check; a chain pair (s, t) is
   the pair of states of two visits of a ranked predicate along one path of it.
   The constraint of the segment -- the clause instances along the path from
   the visit at s to the visit at t, with fresh variables for every node's
   arguments -- is satisfied by the model the derivation gives (every node's
   ground arguments, the clauses' own variables completed by one satisfiability
   call).  Projecting every variable but the two visits' states away at that
   model gives one cube of literals that hold at the model: a convex set of
   pairs that contains (s, t) and implies the existential closure of the
   segment constraint.  So when the segment constraint is the conjunction of
   the instances of a whole derivation fragment, every pair of the region is
   joined by such a fragment: requiring a ranking to contain the region asks
   for no pair a play of the same derivation shape could not produce.  The
   projection is the one MuCyc's refinement runs: model-based projection as
   Komuravelli, Gurfinkel and Chaki define it ("SMT-Based Model Checking for
   Recursive Programs", CAV 2014), per theory as Bjorner and Janota give it
   (LPAR-20, 2015), over the theories [Mbp] implements, the input first reduced
   to the literals the model makes true.  So a segment that is not convex -- a
   disjunction in a clause body -- yields the cube of the disjunct the model
   satisfies. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* [project ~model ~kept phi]: the projection of [phi] onto the variables
   [kept] at [model].

   Pre: [model] assigns a ground term to variables of [phi] and is meant to be
   extendable to a model of [phi] (the projection extends it to [phi]'s other
   free variables by asking Z3).
   Post: [Some region] only when [model] satisfies [phi] (checked here when
   [model] assigns every free variable of [phi]; otherwise the projection's
   own extension of the model refuses an unsatisfiable rest), and [region] is
   quantifier-free, mentions some variable and only variables of [kept], and
   evaluates to true at [model] restricted to [kept] -- so a region always
   contains the model's point, and, the projection's own contract, implies
   the existential closure of [phi] over the variables not in [kept].  [None]
   when any of these fails.  Raises what the projection raises (a [model] that
   cannot be extended to [phi], or a theory the projection does not handle);
   a caller treats that as no region.

   Why the model is checked: the projection reads the sign of every literal
   at [model] and trusts it; at an assignment that falsifies [phi] it returns
   a cube of the literals as that assignment signs them, which can hold at
   the kept point and still describe pairs no instance of [phi] joins. *)
let project ?(print = fun _ -> ()) ~model ~kept phi =
  let kept_set = Set.Poly.of_list (List.map kept ~f:fst) in
  let eliminated =
    Set.filter (Formula.term_sort_env_of phi) ~f:(fun (x, _) ->
        not (Set.mem kept_set x))
  in
  let model_satisfies =
    let phi_m = Evaluator.simplify @@ Formula.subst model phi in
    (not (Set.is_empty (Formula.fvs_of phi_m)))
    ||
      try Evaluator.eval @@ Evaluator.simplify phi_m
      with exn_ when not (Common.Timer.is_async exn_) -> false
  in
  if not model_satisfies then None
  else
    let region =
      Evaluator.simplify
      @@ MbpProject.get_mbp_with
           ~conditionals:(MbpProject.All_paths_up_to 1_000)
           ~check_validity:false ~print model eliminated phi
    in
    let fvs = Formula.fvs_of region in
    let holds =
      try
        Evaluator.eval @@ Evaluator.simplify
        @@ Formula.subst
             (Map.Poly.filter_keys model ~f:(Set.mem kept_set))
             region
      with exn_ when not (Common.Timer.is_async exn_) -> false
    in
    if holds && Set.is_subset fvs ~of_:kept_set && not (Set.is_empty fvs) then
      Some region
    else None

(* [drop_implied ?timeout_ms ?implies region]: [region] with each conjunct
   that the other remaining conjuncts imply removed.

   The conjuncts are visited in the order [Formula.conjuncts_list_of] gives
   them; one equal to a conjunct still kept is dropped without a question,
   and any other is dropped when [implies rest c] answers true, [rest] being
   the conjuncts kept so far and those not yet visited.  The default [implies]
   asks Z3 whether [rest => c] is valid within [timeout_ms] (per question),
   refusing to ask a question whose shape may not return; an undecided or
   refused question keeps the conjunct.

   Post: the result is a conjunction of a sub-list of [region]'s conjuncts, in
   their order, and it is equivalent to [region] whenever every [true] that
   [implies] answered is a valid implication: each drop removes a conjunct the
   rest implies, so the conjunction is unchanged at every step.  A region with
   fewer than two conjuncts is returned as it is.  The cost is at most one
   question per conjunct. *)
let drop_implied ?(timeout_ms = 500) ?implies region =
  let implies =
    match implies with
    | Some f -> f
    | None -> (
        fun rest c ->
          let phi = Formula.mk_imply (Formula.and_of rest) c in
          (not (Z3Smt.Z3interface.may_not_return phi))
          &&
          match
            Z3Smt.Z3interface.check_valid ~timeout:(Some timeout_ms) ~id:None
              (get_fenv ()) phi
          with
          | `Valid -> true
          | _ -> false
          | exception exn_ when not (Common.Timer.is_async exn_) -> false)
  in
  let conjuncts = Formula.conjuncts_list_of region in
  if List.length conjuncts < 2 then region
  else
    let rec go kept = function
      | [] -> List.rev kept
      | c :: todo ->
          if
            List.mem kept c ~equal:Stdlib.( = )
            || implies (List.rev_append kept todo) c
          then go kept todo
          else go (c :: kept) todo
    in
    let kept = go [] conjuncts in
    if List.length kept = List.length conjuncts then region
    else Formula.and_of kept
