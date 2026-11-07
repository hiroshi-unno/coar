open Core
open Ast.LogicOld

(* How to ask a validity question robustly: the strategies that the predicate
   eliminator, the zero-unknown ladder and the validator each used to spell out
   for themselves, written once.

   A caller states its strategy as a value ([strategy]) built from its own
   configuration fields, and keeps its own budgets and its own order of the
   steps that are not shared.  The question rewrites applied before a question
   is asked are part of the strategy ([rewrites], [Ast.QuestionRewrites]: the
   pure ones are applied there, the one that asks a solver here,
   [factor_equalities]).  Three asking strategies are shared:

   - pieces first ([pieces_first], [prove_pieces]): a question whose negation
     normal form splits into several pieces ([ClausePieces]) is asked piece by
     piece before anything else, each piece under short budgets, natively and
     then by cvc5; only proofs and refutations of pieces are read.  A clause is
     the conjunction of its pieces in every model, so a proof of every piece is
     a proof of the question and a countermodel of one piece is one of the
     question; anything else leaves the question to the caller's next step.
     Why: the case splits of a Rust-derived loop's negated postcondition over
     hundreds of shared premise disjuncts are undecided whole within a minute
     by Z3 and cvc5 alike, while cvc5 proves most cases in 0.1-0.4 s each.
   - the cvc5 proof ([cvc5], [proved_by_cvc5]): a question a native ask left
     undecided is given to cvc5 as a process of its own, and only its [unsat]
     of the negation is read, as a proof.  cvc5 never refutes here, so the
     retry can only turn an undecided answer into a proof.
   - the fork policy ([fork_policy], [fork_reason], [check_valid]): a question
     whose shape Z3 may not return on ([Z3interface.may_not_return]: a
     quantifier binding a sequence, say), or any quantified question, is asked
     in a forked copy of the process killed after a wall-clock budget, since
     neither Z3's own budget nor this tree's timer bounds those shapes.

   Contract of every function here: it asks exactly the questions the caller's
   strategy names, in the order stated at the function, with the budgets the
   caller passes; it reads a proof as [`Valid] only when a solver proved the
   question (or every piece of it), and a refutation as [`Invalid] only when a
   solver refuted it (or a piece of it). *)

(* the answer of a validity question, as [Z3interface.check_valid] gives it *)
type 'model answer =
  [ `Valid | `Invalid of 'model | `Timeout | `Unknown of string ]

(* cvc5 asked for a proof: under [ms] milliseconds, with [rlimit] resource
   units per check when given ([--rlimit-per]), logged under [site], the wait
   charged to the phase [phase] of the phase-time account *)
type cvc5 = { ms : int; rlimit : int option; site : string; phase : string }

(* the per-piece budgets of the pieces-first strategy: [z3_ms] for the native
   ask of each piece, [cvc5_ms] (when given) for the cvc5 proof of a piece the
   native ask left undecided.  The configuration fields that set it are
   written [(z3_ms, cvc5_ms)] *)
type pieces_first = { z3_ms : int; cvc5_ms : int option }

let pieces_first_of_pair (z3_ms, cvc5_ms) = { z3_ms; cvc5_ms }

(* which questions are asked in a killed copy instead of in this process:
   [refused] the shapes [Z3interface.may_not_return] refuses, [quantified]
   every other quantified question *)
type fork_policy = { refused : bool; quantified : bool }

let in_process = { refused = false; quantified = false }

(* A caller's strategy.  [fork_margin_ms]: with [Some m], [check_valid] asks a
   quantified question in a copy killed after its budget plus [max m 0] ms;
   the validator, whose questions are satisfiability questions and whose kill
   budget is its own, reads [fork] through [fork_reason] instead. *)
type strategy = {
  rewrites : Ast.QuestionRewrites.t;
  pieces_first : pieces_first option;
  cvc5_retry : cvc5 option;
  fork : fork_policy;
  fork_margin_ms : int option;
}

let plain =
  { rewrites = Ast.QuestionRewrites.none; pieces_first = None; cvc5_retry = None; fork = in_process; fork_margin_ms = None }

(* [fork_reason policy phi]: [`Refused] when [policy.refused] and
   [Z3interface.may_not_return phi]; otherwise [`Quantified] when
   [policy.quantified] and [phi] has a quantifier; otherwise [`Here].  The
   shape test runs only when [policy.refused] is set, and before the
   quantifier test, which runs only when the shape test did not decide. *)
let fork_reason policy phi =
  if policy.refused && Z3Smt.Z3interface.may_not_return phi then `Refused
  else if policy.quantified && not (Formula.is_quantifier_free phi) then
    `Quantified
  else `Here

(* [check_valid ~margin_ms ~timeout ?fresh_solver ~id fenv phi] is
   [Z3interface.check_valid ~timeout:(Some timeout) ?fresh_solver ~id fenv
   phi] unless [margin_ms] is [Some m] and [phi] has a quantifier.  Then the
   same call is made in a forked copy with no Z3 timer (the thread serving one
   does not exist in a forked process; the kill is the budget), killed after
   [timeout + max m 0] ms, and its proof or refutation is read back (charged to
   the phase [fork-quantified]).
   Contract: the result is [`Valid] only if the call answered valid, and
   [`Invalid []] only if it answered invalid, in the copy or here; a copy's
   refutation carries the empty model, because its model (a value of
   extensible variants) does not survive the trip back.  A copy killed, dead
   or raising gives [`Timeout]; when no copy can be forked (other domains
   running, or the memory budget) the question is asked here as with
   [margin_ms = None].  So the copy decides exactly what the in-process call
   would decide before the kill, and no copy outlives the call. *)
let check_valid ~margin_ms ~timeout ?fresh_solver ~id fenv phi =
  let here () =
    Z3Smt.Z3interface.check_valid ~timeout:(Some timeout) ?fresh_solver ~id
      fenv phi
  in
  match margin_ms with
  | Some m when not (Formula.is_quantifier_free phi) -> (
      match
        Common.PhaseTime.with_phase "fork-quantified" @@ fun () ->
        ForkedQuery.run_forked
          ~ms:(timeout + Int.max m 0)
          (fun () ->
            match
              Z3Smt.Z3interface.check_valid ~timeout:None ?fresh_solver ~id
                fenv phi
            with
            | `Valid -> `V
            | `Invalid _ -> `I
            | `Timeout -> `T
            | `Unknown r -> `K r
            | `Sat _ | `Unsat -> `K "unexpected answer")
      with
      | `Value `V -> `Valid
      | `Value `I -> `Invalid []
      | `Value `T | `Lost -> `Timeout
      | `Value (`K r) -> `Unknown r
      | `Not_forked -> here ())
  | _ -> here ()

(* [proved_by_cvc5 ?trace c ~id fenv phi]: whether cvc5 proves [phi] valid
   within [c]'s budgets ([Cvc5Proof.valid_within]), timed as the phase
   [c.phase].  Only a proof is read: [false] is "not proved", never
   "refuted". *)
let proved_by_cvc5 ?trace c ~id fenv phi =
  Common.PhaseTime.with_phase c.phase (fun () ->
      Cvc5Proof.valid_within ?trace ?rlimit:c.rlimit ~site:c.site ~ms:c.ms ~id
        fenv phi)

(* the reason given for a piece the shape test kept from the native solver *)
let not_asked = "not asked: the solver may not return on this shape"

(* [ask_piece ?shape_phase ~native ~cvc5 p]: one piece asked as the
   pieces-first strategy asks it.  In order: the shape test
   ([Z3interface.may_not_return p], timed as [shape_phase] when given); when it
   refuses, [`Unknown not_asked] and the native solver is not asked, otherwise
   [native p] (the caller's native ask, with its budget, context and fork
   policy); then, when that answer is neither a proof nor a refutation and
   [cvc5] is given, [proved_by_cvc5 cvc5], whose proof gives [`Valid] and
   whose failure leaves the native answer. *)
let ask_piece ?shape_phase ~native ~cvc5 ~id fenv p =
  let refused =
    match shape_phase with
    | Some name ->
        Common.PhaseTime.with_phase name (fun () ->
            Z3Smt.Z3interface.may_not_return p)
    | None -> Z3Smt.Z3interface.may_not_return p
  in
  let z = if refused then `Unknown not_asked else native p in
  match (z, cvc5) with
  | (`Valid | `Invalid _), _ | _, None -> z
  | _, Some c -> if proved_by_cvc5 c ~id fenv p then `Valid else z

(* [cvc5_of_pieces_first pf ~rlimit ~site ~phase]: the cvc5 step of [pf] as an
   [ask_piece] argument *)
let cvc5_of_pieces_first pf ~rlimit ~site ~phase =
  Option.map pf.cvc5_ms ~f:(fun ms -> { ms; rlimit; site; phase })

(* [prove_pieces ~ask c] is [ClausePieces.prove_pieces ~ask c]: the pieces of
   [c] asked with [ask], in order, each once, and the whole never; see there
   for the outcome.  The one entry point of the strategy, so that every caller
   splits by the same rule. *)
let prove_pieces ~ask c = ClausePieces.prove_pieces ~ask c

(* [factor_equalities rw ~timeout ~id fenv phi]: with
   [rw.implied_factor_equalities], [phi] with the equations between factors of
   products that its linear facts imply stated as disjuncts
   ([Z3interface.implied_factor_equalities], which asks Z3 under [timeout]),
   an equivalence in every model, timed as [factor-eqs]; [phi] otherwise *)
let factor_equalities (rw : Ast.QuestionRewrites.t) ~timeout ~id fenv phi =
  if rw.implied_factor_equalities then
    Common.PhaseTime.with_phase "factor-eqs" (fun () ->
        Z3Smt.Z3interface.implied_factor_equalities ~timeout ~id fenv phi)
  else phi

(* [with_int_binder_split rw f]: [f ()] with the solver interface's own
   integer-binder split requested when [rw.int_binders] is
   [In_solver_calls]. Otherwise no additional split is requested; an enclosing
   active split remains in force ([Z3interface.with_split_int_binders]). *)
let with_int_binder_split (rw : Ast.QuestionRewrites.t) f =
  Z3Smt.Z3interface.with_split_int_binders
    (match rw.int_binders with In_solver_calls -> true | _ -> false)
    f

