open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* Decide a satisfiability question that [Z3interface.may_not_return] refuses by
   asking a weaker one and checking its model against what was left out.

   Why: a counterexample query of the validator binds a sequence under a
   quantifier when the clause states a premise as a universal over sequences
   (a law inlined from a callee's postcondition, say [forall a s i. produces a s
   x -> produces a (s ++ [i]) y]).  To answer [sat] the solver has to show that
   universal true in the model it is building, which is a validity question
   over sequences inside a model search, and z3 was observed not to answer
   such a query in minutes (nor under a 5 s budget, which does not hold there).
   Without the universal the same query is decided at once, and the universal
   with the model's values substituted is a closed validity question that z3
   refutes by instantiating the law's own index universal (0.04-0.11 s
   observed).  cvc5's model-based instantiation also decides the whole query;
   this tree does not read cvc5's models, so the check is done here. *)

(* [unsat_in_copy ~id ~ms fenv phi] is [true] only when [phi] was found
   unsatisfiable by a forked copy within [ms] ms ([ForkedQuery.run]); a copy
   that runs out of time, raises or answers otherwise gives [false].  No Z3
   timer is armed in the copy, since the thread serving it does not survive
   the fork; the kill is the budget. *)
let unsat_in_copy ~id ~ms fenv phi =
  match
    ForkedQuery.run ~ms (fun () ->
        match Z3Smt.Z3interface.check_sat ~id ~timeout:None fenv [ phi ] with
        | `Unsat -> true
        | _ -> false)
  with
  | Some true -> true
  | _ -> false

(** [model_extends ~id ~ms fenv refused model] is [true] only when, for every
    [c] in [refused], [c] with [model]'s values substituted has an
    unsatisfiable negation (asked by [unsat_in_copy] within [ms]), so that [c]
    holds under [model] for every value of whatever [model] leaves unassigned.
    A model of the other conjuncts of a question for which this is [true]
    extends to a model of the whole question. *)
let model_extends ~id ~ms fenv refused model =
  let sub =
    Common.PhaseTime.with_phase "model-sub" @@ fun () ->
    Map.Poly.of_alist_reduce ~f:(fun t _ -> t)
    @@ List.filter_map model ~f:(function
         | (x, _), Some t -> Some (x, t)
         | _ -> None)
  in
  let holds c =
    let c' =
      Common.PhaseTime.with_phase "subst-simplify" (fun () ->
          Evaluator.simplify (Formula.subst sub c))
    in
    Formula.is_true c'
    || Common.PhaseTime.with_phase "refused-copy" (fun () ->
           unsat_in_copy ~id ~ms fenv (Formula.mk_neg c'))
  in
  List.for_all refused ~f:holds

(** [decide ~id ~timeout fenv neg_phi] splits [neg_phi] into its top-level
    conjuncts, [refused] those [may_not_return] refuses and [rest] the others,
    and asks [rest] in-process with [timeout].

    Contract (the answer is the first component; the second says why):
    - [Some `Unsat] only when [rest] -- implied by [neg_phi] -- is
      unsatisfiable, so [neg_phi] is;
    - [Some (`Sat m)] only when [m] is [rest]'s model and, for every [c] in
      [refused], [c] with [m]'s values substituted has an unsatisfiable
      negation (asked by [unsat_in_copy] with [timeout], 10 s when none), so
      that [c] holds under [m] for every value of whatever [m] leaves
      unassigned, and [m] so extended satisfies [neg_phi];
    - [None] when [refused] or [rest] is empty, [rest] is undecided, or some
      refused conjunct is not shown to hold under [m].  A [None] says nothing
      about [neg_phi]: the caller asks it as it would without this function. *)
let decide ~id ~timeout fenv neg_phi =
  let refused, rest =
    Common.PhaseTime.with_phase "partition" (fun () ->
        List.partition_tf (Formula.conjuncts_list_of neg_phi)
          ~f:Z3Smt.Z3interface.may_not_return)
  in
  if List.is_empty refused then (None, "nothing is refused")
  else if List.is_empty rest then (None, "every conjunct is refused")
  else
    let ms = Option.value timeout ~default:10000 in
    match
      Common.PhaseTime.with_phase "rest" (fun () ->
          Z3Smt.Z3interface.check_sat ~id ~timeout fenv [ Formula.and_of rest ])
    with
    | `Unsat -> (Some `Unsat, "the rest is unsat")
    | `Sat model ->
        if model_extends ~id ~ms fenv refused model then
          ( Some (`Sat model),
            "the rest is sat and its model satisfies the dropped conjuncts" )
        else (None, "the rest's model is not shown to satisfy a dropped conjunct")
    | `Timeout -> (None, "the rest timed out")
    | `Unknown r -> (None, "the rest is unknown " ^ r)

(** [rest_unsat ~id ~timeout fenv neg_phi] is [true] only when [neg_phi] has a
    top-level conjunct [may_not_return] refuses and one it does not, and the
    conjunction [rest] of the latter is found unsatisfiable, in a fresh Z3
    context within [timeout] ms.  The same partition as [decide], with only its
    [`Unsat] side: no model of [rest] is checked against the dropped conjuncts,
    so a [false] says nothing about [neg_phi].

    Sound as a proof that [neg_phi] is unsatisfiable: [neg_phi] is the
    conjunction of [rest] and the refused conjuncts, so it implies [rest]; Z3's
    [unsat] of [rest] says no structure of the theory and no value of [rest]'s
    free variables and uninterpreted symbols satisfies it, so none satisfies
    [neg_phi] either.  [rest] is asked in-process: each of its conjuncts passed
    [may_not_return], so a solver budget holds on it.  An exception other than
    an asynchronous one (a timeout, an interrupt) gives [false]. *)
let rest_unsat ~id ~timeout fenv neg_phi =
  let refused, rest =
    List.partition_tf (Formula.conjuncts_list_of neg_phi)
      ~f:Z3Smt.Z3interface.may_not_return
  in
  (not (List.is_empty refused))
  && (not (List.is_empty rest))
  &&
  try
    match
      Z3Smt.Z3interface.check_sat ~id ~timeout:(Some timeout)
        ~fresh_solver:true fenv [ Formula.and_of rest ]
    with
    | `Unsat -> true
    | _ -> false
  with exn when not (Common.Timer.is_async exn) -> false

(** [prove_refused ~id ~budget phi] is the zero-unknown verdict's use of
    [rest_unsat] for a validity question [phi] that [may_not_return] refuses:
    [false] when [budget] is [None], and otherwise whether the weakened negation
    of [phi] (its negation in negation normal form, defined functions those it
    reaches) is shown unsatisfiable within [budget] ms.  A [true] proves [phi]
    valid in every model of the theory, every term the theory leaves open taking
    every value, which is the reading under which the verdict reads an [unsat]
    of [not phi] as [`Valid]; a [false] says nothing about [phi]. *)
let prove_refused ~id ~budget phi =
  match budget with
  | None -> false
  | Some ms ->
      let neg = Formula.nnf_of (Formula.negate phi) in
      rest_unsat ~id ~timeout:ms
        (Z3Smt.Z3interface.fenv_reached_by (get_fenv ()) neg)
        neg

(** [discharge_in_copy ~id ~ms fenv cond] decides a guard the same way:
    [`Sat] (the guard is VALID) when its negation is shown unsatisfiable in a
    forked copy, [`Unsat] when the guard itself is, [`Unknown] otherwise.  It
    is meant for a guard [may_not_return] refuses, which an in-process
    question may not return on; for any other guard it answers as the two
    in-process questions would, only slower. *)
let discharge_in_copy ~id ~ms fenv cond =
  if unsat_in_copy ~id ~ms fenv (Formula.mk_neg cond) then `Sat
  else if unsat_in_copy ~id ~ms fenv cond then `Unsat
  else `Unknown

(* [leaves_cells_undecided ~weaken ~keep_cells] is whether the truth table
   stops asking a cell whose validity question [Z3interface.may_not_return]
   refuses ([TruthTable.leave_unreturnable_cells_undecided]).  Weakening sets
   it, because an example derived from a weakened counterexample carries the
   dropped law in its guard; [keep_cells] keeps the cells asked as they are
   without weakening (in process, with the truth table's own budget if any), at
   the risk the flag guards against: such a question may not return. *)
let leaves_cells_undecided ~weaken ~keep_cells = weaken && not keep_cells
