(** Validator *)

open Core
open Common
open Common.Ext
open Common.Combinator
open PCSatCommon
open Ast
open Ast.LogicOld

module type ValidatorType = sig
  val run_phase : int -> State.s -> State.u Or_error.t

  val houdini_before_synthesis : State.u -> State.u option
  (** the Houdini-style pre-pass over the declared candidate atoms, asked once
      before the first synthesis; [None] leaves the loop as it would have
      been; with [houdini.schedule.after_ms = Some _] it always gives [None] *)

  val houdini_at_round_boundary : elapsed_s:float -> State.u -> State.u option
  (** the same pre-pass asked lazily at a round boundary after the first,
      [elapsed_s] seconds after the coordinator's loop started: it runs only
      with [houdini.schedule = Before_synthesis { after_ms = Some t; _ }],
      [elapsed_s] at least [t] milliseconds and the pre-pass not yet run in
      this solve; [None] otherwise and whenever the eager form
      would give [None] *)

  val houdini_in_parallel : bool
  (** whether the configuration's [houdini.schedule] is [Parallel]: the
      coordinator races the pre-pass in a
      forked copy ([houdini_parallel_prepass]) against the loop, and the two
      forms above then give [None] *)

  val houdini_parallel_prepass : State.u -> State.u option
  (** the pre-pass as the forked copy of [houdini.schedule = Parallel _] runs it, under
      [houdini.schedule.budget] (else [houdini.budget_ms]): [Some (Sat
      sol)] for a fixed point that passed the final check at any time, the
      state with its counterexamples added for one that did not when that
      came within [houdini.budget_ms] (and [houdini.feedback_counterexamples]
      is on), [None] otherwise *)

  val houdini_seq_instantiation : bool
  (** the configuration's [houdini.questions.seq_instantiation]: whether the pre-pass
      asks its sequence-existential questions by witness instantiation, for
      which the caller must set [SeqInstantiation]'s switches first *)
end

(** configuration of validator *)
module Config = ValidatorConfig

(* The candidate atoms and the countermodel judgement of the Houdini-style
   pre-pass live in the library [Houdini]; the aliases keep the names the
   pre-pass below uses. *)
module HoudiniCandidates = Houdini.Candidates
module HoudiniByModel = Houdini.ByModel

module Make
    (RLCfg : RLConfig.ConfigType)
    (Cfg : Config.ConfigType)
    (APCSP : PCSP.Problem.ProblemType) = struct
  let config = Cfg.config
  let id = PCSP.Problem.id_of APCSP.problem

  (* a counterexample found by [weaken_and_model_check] carries the dropped
     law in the guard of the examples derived from it, and a truth-table cell
     over that guard is a validity question of the same refused shape, so the
     weakening leaves such cells undecided unless
     [questions.weaken.keep_cells] asks for them to be asked *)
  let () =
    if
      PCSatCommon.WeakenedQuery.leaves_cells_undecided
        ~weaken:(ValidatorConfig.QuestionsSwitch.weaken_unreturnable_queries config)
        ~keep_cells:(ValidatorConfig.QuestionsSwitch.weaken_unreturnable_keep_cells config)
    then PCSatCommon.TruthTable.leave_unreturnable_cells_undecided := true

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id

  (* The fact clauses of the problem this phase validates against, each as the
     formula [find_all_counterexamples] meets it in (the key) and the example
     that is the clause itself: the head atom guarded by the negated pure part,
     parametric in every variable.  A clause is [phi \/ ps \/ not ns], so a
     fact [ns = {}], [ps = {P(t)}] reads [not phi => P(t)].  Keyed on the
     formula because that is all the caller keeps of a clause, and computed from
     it by the same function the caller used, so equal clauses give equal
     keys.  The builder is [FactExample.of_clause]. *)
  let fact_examples =
    lazy
      (let exi_senv = PCSP.Problem.senv_of APCSP.problem in
       Set.to_list (PCSP.Problem.clauses_of APCSP.problem)
       |> List.filter_map ~f:(fun cl ->
           Option.map (PCSatCommon.FactExample.of_clause exi_senv cl)
             ~f:(fun ex -> (snd (Clause.to_senv_formula cl), ex))))

  let fact_example_of clause =
    List.Assoc.find (Lazy.force fact_examples) clause ~equal:Stdlib.( = )

  (* A clause violated by a model falsifies every one of its disjuncts, so an
     existential disjunct -- which is what a premise stated with a universal
     quantifier becomes in negation normal form -- is false there, and its body
     is false at *every* point.  Instantiating that at the terms the
     counterexample itself uses gives facts which hold wherever the example
     does.  They are attached to the example as a condition, which makes it
     weaker on purpose: the candidate is then asked to satisfy the example only
     in the situations the premise admits, which is the obligation the clause
     states and not the stronger one the example alone expresses. *)
  let premise_instances_of sub phi =
    let terms =
      List.dedup_and_sort ~compare:Stdlib.compare @@ Map.Poly.data sub
    in
    let facts =
      Set.fold (Formula.disjuncts_of phi) ~init:[] ~f:(fun acc d ->
          match d with
          | Formula.Bind (Formula.Exists, bounds, body, _)
            when List.length bounds <= 2 && Set.is_empty (Formula.pvs_of body)
            ->
              List.fold bounds ~init:acc ~f:(fun acc (v, sort) ->
                  List.fold terms ~init:acc ~f:(fun acc t ->
                      if Stdlib.(Term.sort_of t = sort) then
                        Formula.mk_neg
                          (Formula.subst (Map.Poly.singleton v t) body)
                        :: acc
                      else acc))
          | _ -> acc)
    in
    if List.is_empty facts then None
    else Some (Evaluator.simplify @@ Formula.and_of facts)

  (* for [ExClause.make]: does some model of the theory satisfy the ground
     guard a counterexample left on its atoms?  The guard is quantifier-free
     and small, so the budget matches the neighbouring preprocessing queries;
     undecided keeps the guard, which is the safe direction. *)
  (* the numeric literals the PROBLEM states, computed once.  A counterexample's
     model assigns a value to every variable its query constrains whether or not
     the constraint forces it, and marks only what it chose to mark, so nothing
     in the model separates a value the program states from one the solver
     invented.  This set is the cheap separator: measured on one run of a
     Rust-derived refutation, 292 of 388 integer occurrences written into the
     examples were one of the four values the problem states and 96 were one of
     fifteen it never mentions.  It is a heuristic for "was the value forced",
     and the guard the opened variable keeps is what makes the result sound
     whichever way it guesses. *)
  let stated_literals =
    lazy
      (Set.concat_map
         (PCSP.Problem.old_formulas_of APCSP.problem)
         ~f:LogicOld.abs_num_literals_of_formula)

  (* Decide a ground guard that the pure part left undecided, for the caller
     that turns [cond => +/-P(t)] into an unconditional atom.

     SATISFIABILITY DOES NOT LICENSE DROPPING THE GUARD, and reading it as
     though it did produced a certified refutation of a satisfiable system.  A
     solution has to make [cond => P(t)] hold in every model of the theory,
     which forces [P(t)] only in the models where [cond] holds; an
     unconditional atom claims it in all of them, and that needs [cond] to be
     VALID.  Where [cond] is merely satisfiable the claim is about a
     sub-family of models, and two such claims can rest on families that are
     disjoint: a positive guarded by an equation and a negative guarded by its
     negation are each satisfiable, both were discharged, and the resulting
     atoms collided into a refutation although no single model established
     both.  Two external solvers answer "satisfiable" on that input and a
     solution can be written down.

     Nothing is lost by keeping such a guard, because the conflict test that
     compares two examples conjoins their guards and asks whether THAT is
     satisfiable -- which is the sound version of the same reasoning, and is
     what still refutes a guarded example against an unconditional one.

     Three answers, and the two that are not [`Sat] are unchanged: an
     unsatisfiable guard means the clause says nothing and it is dropped, and
     anything undecided keeps the guard, which is always sound. *)
  let discharge fenv cond =
    if
      (ValidatorConfig.QuestionsSwitch.weaken_unreturnable_queries config)
      && Z3Smt.Z3interface.may_not_return cond
    then
      (* The guard of an example derived from a counterexample that
         [weaken_and_model_check] found is the law it dropped, with the
         model's values in it, and it was shown valid there by the same
         question; asked in-process, a guard of this shape keeps its law, and
         a synthesis query over such guards was observed not to return.  The
         two questions are asked in a forked copy, with the budget of the
         in-process ones. *)
      PCSatCommon.WeakenedQuery.discharge_in_copy ~id ~ms:1000 fenv cond
    else
    match
      Z3Smt.Z3interface.check_sat ~id ~timeout:(Some 1000) fenv [ cond ]
    with
    | `Unsat -> `Unsat
    | `Sat _ -> (
        match
          Z3Smt.Z3interface.check_sat ~id ~timeout:(Some 1000) fenv
            [ LogicOld.Formula.mk_neg cond ]
        with
        | `Unsat -> `Sat
        | _ -> `Unknown)
    | _ -> `Unknown

  (* The names [skolemize_positive_existentials] introduced for a query when
     [examples.record.head_witnesses] is on, so that the model a counterexample is built
     from can be asked which of its entries are witnesses.  Every name is
     fresh, so the set only grows and a name never means anything else;
     compare-and-set keeps domains asking at once from dropping each other's
     names. *)
  let head_witness_vars : Ident.tvar Set.Poly.t Atomic.t = Atomic.make Set.Poly.empty

  let rec note_head_witness_vars vars =
    let old = Atomic.get head_witness_vars in
    let updated = Set.union old (Set.Poly.of_list (List.map vars ~f:fst)) in
    if not (Atomic.compare_and_set head_witness_vars old updated) then
      note_head_witness_vars vars

  (* The integer values [model] gives the witness names of
     [head_witness_vars], deduplicated. *)
  let head_witness_values model =
    let names = Atomic.get head_witness_vars in
    List.dedup_and_sort ~compare:Z.compare
    @@ List.filter_map model ~f:(fun ((x, _), v) ->
           match v with
           | Some t when Set.mem names x -> (
               match Term.value_of (Evaluator.simplify_term t) with
               | Value.Int z -> Some z
               | _ -> None
               | exception exn_ when not (Common.Timer.is_async exn_) -> None)
           | _ -> None)

  (* [phi] is valid exactly when its negation is unsatisfiable, so the check
     asks for a counterexample instead.  The negation keeps its own name: the
     trace line reports what was asked, and shadowing [phi] made it read as
     though the clause itself had been handed to the solver. *)
  (* Replace each POSITIVE existential by fresh free variables, returning them
     so that the model can be asked what it chose.  Positive means: reached
     through conjunction and disjunction only.  The walk stops at a negation
     and at a universal, where a constant would not be sound -- under a
     universal the witness depends on it and skolemisation needs a function,
     whose interpretation this tree's model reader drops anyway. *)
  let skolemize_positive_existentials phi =
    let vars = ref [] in
    let rec walk phi =
      match phi with
      | Formula.Bind (Formula.Exists, bounds, body, _) ->
          let sub =
            Map.Poly.of_alist_exn
            @@ List.map bounds ~f:(fun (x, s) ->
                   let x' = Ident.mk_fresh_tvar () in
                   vars := (x', s) :: !vars;
                   (x, Term.mk_var x' s))
          in
          walk (Formula.subst sub body)
      | Formula.BinaryOp (Formula.And, p, q, _) ->
          Formula.mk_and (walk p) (walk q)
      | Formula.BinaryOp (Formula.Or, p, q, _) ->
          Formula.mk_or (walk p) (walk q)
      | phi -> phi
    in
    let phi = walk phi in
    (phi, !vars)

  (* Drop a universal or existential none of whose variables occurs free in
     its body, as in [exists j. false] or [forall j. true], which the read-back
     of a celled candidate leaves behind once its body has simplified away.
     The result is equivalent, every sort here being non-empty.  It is used
     only to decide whether a counterexample query is quantifier-free enough to
     be re-asked with a preference: such a leftover binder is no reason to
     fear that the re-asked query will not return. *)
  let rec drop_vacuous_binders phi =
    match phi with
    | Formula.Bind ((Formula.Forall | Formula.Exists), bounds, body, _) ->
        let body = drop_vacuous_binders body in
        let fvs = Formula.tvs_of body in
        if List.exists bounds ~f:(fun (x, _) -> Set.mem fvs x) then
          (match phi with
          | Formula.Bind (Formula.Forall, _, _, _) -> Formula.forall bounds body
          | _ -> Formula.exists bounds body)
        else body
    | Formula.BinaryOp (Formula.And, p, q, _) ->
        Formula.mk_and (drop_vacuous_binders p) (drop_vacuous_binders q)
    | Formula.BinaryOp (Formula.Or, p, q, _) ->
        Formula.mk_or (drop_vacuous_binders p) (drop_vacuous_binders q)
    | Formula.UnaryOp (Formula.Not, p, _) -> Formula.mk_neg (drop_vacuous_binders p)
    | phi -> phi

  (* The budgets of the questions [check_clause_readback] asks beside the
     unrewritten one.  An instantiated form and a pinned negation bind no
     sequence, so the solver's own budget is expected to hold for them, which
     it does not over a quantified sequence.  The values are a choice with
     room above the decided questions' times recorded when this was written,
     not a measured bound. *)
  let readback_instance_timeout = Some 10000
  let readback_full_timeout = Some 10000
  let readback_pinned_timeout = Some 5000
  let readback_retry_timeout = 5000

  (* The wall-clock deadline of the Houdini pre-pass while it runs with
     [houdini.budget_ms] ([None] at every other time, so nothing below changes
     a question asked outside the pre-pass).  While it is set, every solver
     question the validator asks -- the pre-pass's own and its final check's --
     is given at most what is left of it ([cap_timeout]), a question with no
     budget of its own included; a validation query of the default
     configuration has none, and one of the final check's questions ran past
     70 s and out of memory on an input the loop answers in 2 s. *)
  let houdini_window = Houdini.Window.create ()
  let houdini_deadline = houdini_window.deadline

  (* [houdini.questions.atom_countermodel_drops]: while one atom's question of the
     fixed point is asked, the question as it reaches
     [check_clause_nonparam_smt] (compared by physical identity) and the
     judge of the clause's atoms still to be asked, which gives the positions
     of those a model of the question's negation makes false; and the
     positions a countermodel of that question refuted, once it has been
     answered.  Both are cleared by the fixed point after each question. *)
  let houdini_pending_judge = houdini_window.pending_judge
  let houdini_judged_drops = houdini_window.judged_drops

  (* how many atoms a reused countermodel dropped without a question of their
     own; read by the tests *)
  let houdini_atom_model_drops = houdini_window.atom_model_drops

  (* how many questions of the fixed point were proved against the body held
     once per clause ([houdini.questions.shared_body_session]); read by the tests *)
  let houdini_shared_body_proofs = houdini_window.shared_body_proofs

  (* how many were refuted there by a model every conjunct set aside holds
     under; read by the tests *)
  let houdini_shared_body_refutations = houdini_window.shared_body_refutations

  (* set by [houdini.questions.shared_body_session] for the next question only, when
     the fixed point's solver has just found the body's other conjuncts and
     the head's negation satisfiable by a model that does not extend: the
     weakened question asks exactly that again, so the question goes straight
     to the forked copy *)
  let houdini_skip_weakened_once = houdini_window.skip_weakened_once

  (* the judge of [houdini_pending_judge] applied to [model], when [phi] is
     the very question it was set for; an exception of the judge drops
     nothing *)
  let judge_pending_atoms phi model =
    Houdini.Window.judge_pending houdini_window phi model

  (* [true] while the pre-pass's final check of its fixed point runs, for
     [houdini.final_check.seq_axiom_first] *)
  let houdini_in_final = houdini_window.in_final

  (* the milliseconds left before the deadline, [None] when none is set *)
  let houdini_remaining_ms () = Houdini.Window.remaining_ms houdini_window
  let houdini_budget_spent () = Houdini.Window.budget_spent houdini_window

  let houdini_budget_nearly_spent () =
    Houdini.Window.budget_nearly_spent houdini_window

  (* [t] capped by the remainder of the pre-pass's deadline, when one is set
     ([Houdini.Window.cap_timeout]) *)
  let cap_timeout (t : int option) = Houdini.Window.cap_timeout houdini_window t

  let cap_ms t = Option.value (cap_timeout (Some t)) ~default:t

  let reads_sequence phi =
    Set.exists (Formula.funsyms_of phi) ~f:(function
      | T_seq.SqNth _ -> true
      | _ -> false)

  let elapsed_since started =
    Time_float.Span.to_sec (Time_float.diff (Common.Clock.now_float ()) started)

  (* [PCSatCommon.WeakenedQuery.decide], traced *)
  let weaken_and_model_check ~timeout fenv neg_phi =
    let started = Common.Clock.now_float () in
    let res, outcome =
      PCSatCommon.WeakenedQuery.decide ~id ~timeout fenv neg_phi
    in
    Debug.print
    @@ lazy
         (sprintf "[weakened query] %s in %.3f s" outcome
            (elapsed_since started));
    (* with COAR_COUNT_MAY_NOT_RETURN, which way each weakened question went,
       counted under the open phase; decides nothing *)
    if Z3Smt.Z3interface.count_may_not_return then
      Common.PhaseTime.event_here
        (match res with
        | Some `Unsat -> "weakened:unsat"
        | Some (`Sat _) -> "weakened:sat"
        | _ -> "weakened:undecided");
    res

  (* the counterexample question of a clause [phi] as [check_clause_nonparam_smt]
     asks it, before its witness skolemization: [phi]'s negation, simplified,
     its sequence reads of concatenations split with [questions.rewrites.split_seq_reads] *)
  let negation_asked phi =
    let neg_phi = Evaluator.simplify @@ Formula.mk_neg phi in
    if config.questions.rewrites.split_seq_reads then Evaluator.rewrite_seq_read_over_concat neg_phi
    else neg_phi

  (* how many satisfiable answers of a forked copy were asked again in this
     process for their model; read by the tests *)
  let forked_sat_reasks = ref 0

  (* how many counterexample queries were asked in this process in a context
     of their own ([questions.fresh_context_quantified]); read by the tests *)
  let fresh_context_asked = ref 0

  (* The in-process counterexample query [neg_phi] of a clause.  Contract:
     the answer of [Z3interface.check_sat] on [neg_phi] with [timeout]; with
     [questions.fresh_context_quantified] and a quantifier in [neg_phi], asked
     as the Z3 interface's measurement mode (COAR_Z3_ALWAYS_FRESH=1) asks it
     ([Z3interface.check_sat_fresh]: a context of its own, the negation normal
     form of [neg_phi], which is equivalent to it, and the definitions it
     reaches), so a model is a model of [neg_phi] and [`Unsat] means [neg_phi]
     has none; a shape that check refuses ([may_not_return]) and everything
     quantifier-free are asked in the pooled context as before. *)
  let ask_counterexample_query ~timeout fenv neg_phi =
    match
      if
        config.questions.fresh_context_quantified
        && not (Formula.is_quantifier_free neg_phi)
      then (
        let r =
          Z3Smt.Z3interface.check_sat_fresh ~timeout ~id fenv [ neg_phi ]
        in
        if Option.is_some r then incr fresh_context_asked;
        r)
      else None
    with
    | Some res -> res
    | None -> Z3Smt.Z3interface.check_sat ~id ~timeout fenv [ neg_phi ]

  (* [ask_counterexample_query], with [questions.scoped_first]
     preceded by the scoped ask of [Z3interface.check_sat_scoped_first]; the
     scoped ask's answer and time are counted under
     [validation-q/scoped-first/<answer>] with the phase-time report on *)
  let ask_in_process ~timeout fenv neg_phi =
    let t0 = Common.PhaseTime.now () in
    let on_scoped r =
      let tag =
        match r with
        | `Unsat -> "unsat"
        | `Sat _ -> "sat"
        | `Timeout -> "timeout"
        | `Unknown _ -> "unknown"
      in
      Debug.print @@ lazy (sprintf "[scoped first] %s" tag);
      if !Common.PhaseTime.on then
        Common.PhaseTime.add ("validation-q/scoped-first/" ^ tag)
          (Common.PhaseTime.now () -. t0)
    in
    let res, _path =
      Z3Smt.Z3interface.check_sat_scoped_first ~on_scoped
        ~enabled:(ValidatorConfig.QuestionsSwitch.scoped_first_quantified_validation config)
        ~scoped_ms:(ValidatorConfig.QuestionsSwitch.scoped_first_quantified_validation_ms config) ~timeout ~id
        fenv [ neg_phi ] ~ask:(fun () ->
          ask_counterexample_query ~timeout fenv neg_phi)
    in
    res

  (* how many undecided clause questions were asked of cvc5
     ([questions.clause_check.cvc5_retry_ms]), and how many of them it proved valid;
     read by the tests *)
  let cvc5_retry_asked = ref 0

  let cvc5_retry_proved = ref 0

  (* how many undecided clause questions were asked again in the axiom form
     ([questions.clause_check.seq_axiom_fallback]); read by the validation dump *)
  let clause_check_seq_axiom_asked = ref 0

  (* [true] while a validation question whose axiom form was already asked
     first ([axiom_first_when_proved] of [questions.clause_check.seq_axiom_fallback]) is
     asked natively, so that
     the axiom form is not asked a second time *)
  let suppress_clause_axiom_fallback = ref false

  (* which counterexample queries are asked in a killed copy, as the validity
     service's fork policy: a shape [may_not_return] refuses under
     [questions.unreturnable], and every other quantified one when
     [questions.unreturnable.scope] is set too (it acts only with the first).  The
     copy's budget is this module's own ([ForkedQuery.kill_ms]) *)
  let fork_policy =
    {
      PCSatCommon.ValidityAsk.refused = (ValidatorConfig.QuestionsSwitch.fork_unreturnable_queries config);
      quantified =
        (ValidatorConfig.QuestionsSwitch.fork_unreturnable_queries config) && (ValidatorConfig.QuestionsSwitch.fork_quantified_queries config);
    }

  (* [verdict_only]: the caller reads only which of [`Sat], [`Unsat],
     [`Timeout] and [`Unknown] the answer is, never a model, so a forked
     copy's [`Sat] is returned with an empty model instead of being asked
     again here; it is ignored when the model is needed for a witness
     ([examples.record.cell_witnesses]) *)
  let check_clause_nonparam_smt ?(timeout = None) ?(verdict_only = false) fenv
      phi =
    let timeout = cap_timeout timeout in
    let neg_phi =
      Common.PhaseTime.with_phase "negate" (fun () -> negation_asked phi)
    in
    let neg_phi, witness_vars =
      if config.examples.record.cell_witnesses || config.examples.record.head_witnesses then
        skolemize_positive_existentials neg_phi
      else (neg_phi, [])
    in
    if config.examples.record.head_witnesses then note_head_witness_vars witness_vars;
    Debug.print
    @@ lazy (sprintf "[check valid -> sat] %s" @@ Formula.str_of neg_phi);
    let weakened =
      if
        (ValidatorConfig.QuestionsSwitch.weaken_unreturnable_queries config)
        && Z3Smt.Z3interface.may_not_return neg_phi
      then weaken_and_model_check ~timeout fenv neg_phi
      else None
    in
    (* inside the Houdini pre-pass's window a question that may not return is
       always asked in a killed copy: its budget is the remainder, and the
       solver's own budget does not hold over it (a final check of the
       pre-pass ran past 50 s and out of memory under a 28 s one) *)
    let houdini_fork =
      Option.is_some !houdini_deadline
      && Common.PhaseTime.with_phase "may-not-return" (fun () ->
             Z3Smt.Z3interface.may_not_return neg_phi)
    in
    (* [houdini.questions.weaken_unreturnable]: the weakened question before the killed
       copy; [None] from it leaves the question to the copy as before *)
    let skip_weakened = !houdini_skip_weakened_once in
    houdini_skip_weakened_once := false;
    let weakened =
      if
        Option.is_none weakened && houdini_fork
        && config.houdini.questions.weaken_unreturnable
        && not skip_weakened
      then
        Common.PhaseTime.with_phase "weakened" (fun () ->
            weaken_and_model_check ~timeout fenv neg_phi)
      else weakened
    in
    (* [houdini.final_check.seq_axiom_first]: in the pre-pass's final check, a
       clause over sequences is first asked in the axiom form, and a proof
       there is the answer ([`Unsat]: no model of the negation exists);
       otherwise the question is asked as before, without the fallback
       asking the axiom form a second time *)
    let axiom_first =
      config.houdini.final_check.seq_axiom_first && !houdini_in_final
      && Option.is_none weakened
    in
    let axiom_proved =
      axiom_first
      &&
      match
        Common.PhaseTime.with_phase "seq-axiom-first" (fun () ->
            Z3Smt.Z3interface.with_seq_axiom_fallback ~caller_timeout:timeout
              ~id fenv phi `Timeout)
      with
      | `Valid ->
          Debug.print
          @@ lazy "[clause check] proved valid by the sequence axioms first";
          true
      | _ -> false
    in
    (* a model of [neg_phi] found in this process, judged against the atoms
       still to be asked ([houdini.questions.atom_countermodel_drops]) *)
    let in_process_judged res =
      (match res with
      | `Sat m when not (List.is_empty m) ->
          Option.iter (judge_pending_atoms phi m) ~f:(fun d ->
              houdini_judged_drops := Some d)
      | _ -> ());
      res
    in
    let res =
      if axiom_proved then `Unsat
      else
      match weakened with
      | Some res -> in_process_judged res
      | None ->
      (* a query that may not return keeps its forked, killed copy: asking it
         in this process under Z3's own budget, which does not hold on those
         shapes, would trade the kill for a hang, on queries that need not
         involve arrays at all *)
      (* [fork_by_quantifier]: forked only because of
         [questions.unreturnable.scope], a shape [may_not_return] does not refuse.
         Counted under [validation-q/forked-quantified/<answer>] with the
         phase-time report on, so a run says whether the switch changed the
         route of any question; the evaluation order is the one before *)
      (* the validity service's fork decision under this module's policy:
         the shape test only with [questions.unreturnable], and the
         quantifier test only when that did not decide and
         [questions.unreturnable.scope] is set too *)
      let fork_reason =
        PCSatCommon.ValidityAsk.fork_reason fork_policy neg_phi
      in
      let fork_unreturnable =
        match fork_reason with `Refused -> true | _ -> false
      in
      let fork_by_quantifier =
        match fork_reason with `Quantified -> true | _ -> false
      in
      let fork_wanted = fork_unreturnable || fork_by_quantifier in
      let pointwise =
        if config.questions.array_pointwise_elim && not houdini_fork then
          Common.PhaseTime.with_phase "array-pointwise" (fun () ->
              let res, why =
                Z3Smt.Z3interface.check_sat_array_pointwise ~id ~timeout fenv
                  [ neg_phi ]
              in
              (if !Common.PhaseTime.on then
                 let o =
                   match res with
                   | Some (`Sat _) -> "sat"
                   | Some `Unsat -> "unsat"
                   | _ -> "fallback"
                 in
                 Common.PhaseTime.add ("validation-q/array-pointwise/" ^ o) 0.);
              Debug.print
              @@ lazy (sprintf "[array pointwise] %s" why);
              res)
        else None
      in
      match pointwise with
      | Some res -> in_process_judged res
      | None ->
      if config.questions.arrays_as_functions && (not houdini_fork) && not fork_wanted
      then (
        let res, outcome =
          (* a question outside the fragment, or one the translation leaves
             undecided, is asked by [ask_in_process] as without the switch,
             so [questions.fresh_context_quantified] and
             [questions.scoped_first] still decide how; asked
             with [check_sat] instead, they were inert on every question
             once this switch was on, array-free ones included *)
          Z3Smt.Z3interface.check_sat_arrays_as_functions ~id ~timeout
            ~untranslated:(fun () -> ask_in_process ~timeout fenv neg_phi)
            fenv [ neg_phi ]
        in
        Debug.print
        @@ lazy
             (sprintf "[arrays as functions] %s: %s"
                (match outcome with
                | `Decided -> "decided as functions"
                | `Fallback r -> "asked as arrays after " ^ r
                | `Outside r -> "outside the fragment, " ^ r)
                (match res with
                | `Sat _ -> "sat"
                | `Unsat -> "unsat"
                | `Timeout -> "timeout"
                | `Unknown r -> "unknown " ^ r));
        (* judged like every other answer found in this process: without
           it a countermodel read here never dropped the Houdini pre-pass's
           atoms it refutes, and once quantified questions stopped being
           forked by default (the forked copy judges them) the pre-pass
           dropped none at all and asked every atom's question itself *)
        in_process_judged res)
      else if houdini_fork || fork_wanted then (
        (* no Z3 timer in the copy: the kill is the budget, and the thread
           that serves a Z3 timer does not exist in a forked process *)
        let ms =
          if houdini_fork then Option.value timeout ~default:10000
          else
            PCSatCommon.ForkedQuery.kill_ms
              ~kill_ms:(ValidatorConfig.QuestionsSwitch.fork_unreturnable_kill_ms config) ~timeout
        in
        let started = Common.Clock.now_float () in
        let res =
          (* only the verdict comes back: a model holds sorts and terms of
             extensible variants, which do not survive marshalling.  A
             satisfiable query is asked again here for its model; the copy
             held this process's solver state, so the same question returns
             here as it did there. *)
          match
            Common.PhaseTime.with_phase "forked" @@ fun () ->
            PCSatCommon.ForkedQuery.run ~ms (fun () ->
                match
                  Z3Smt.Z3interface.check_sat ~id ~timeout:None
                    ~fresh_solver:(houdini_fork && config.houdini.questions.fork_fresh_context)
                    fenv [ neg_phi ]
                with
                | `Sat m ->
                    (* [houdini.questions.atom_countermodel_drops]: the copy holds the
                       model, so the atoms still to be asked are judged here
                       and only their positions are sent back *)
                    `S (judge_pending_atoms phi m)
                | `Unsat -> `U
                | `Timeout -> `T
                | `Unknown r -> `K r)
          with
          | Some (`S drops) when verdict_only && List.is_empty witness_vars ->
              houdini_judged_drops := drops;
              `Sat []
          | Some (`S _) ->
              Int.incr forked_sat_reasks;
              in_process_judged
                (ask_counterexample_query ~timeout fenv neg_phi)
          | Some `U -> `Unsat
          | Some `K r -> `Unknown r
          | Some `T | None -> `Timeout
        in
        (if fork_by_quantifier && (not houdini_fork) && !Common.PhaseTime.on
         then
           Common.PhaseTime.add
             ("validation-q/forked-quantified/"
             ^
             match res with
             | `Sat _ -> "sat"
             | `Unsat -> "unsat"
             | `Timeout -> "killed-or-timeout"
             | `Unknown _ -> "unknown")
             (elapsed_since started));
        Debug.print
        @@ lazy
             (sprintf "[forked query] %s in %.3f s (budget %d ms)"
                (match res with
                | `Sat _ -> "sat"
                | `Unsat -> "unsat"
                | `Timeout -> "killed or timeout"
                | `Unknown r -> "unknown " ^ r)
                (elapsed_since started) ms);
        res)
      else
        in_process_judged (ask_in_process ~timeout fenv neg_phi)
    in
    (* [questions.clause_check.seq_axiom_fallback]: an undecided question is asked once
       more as the validity of [phi] in the axiom form; only a proof is read,
       as [`Unsat] (no model of the negation exists), so a decided answer and
       an unproved one are left as they were *)
    let res =
      match res with
      | (`Timeout | `Unknown _)
        when Config.clause_axiom_fallback_on config.questions.clause_check.seq_axiom_fallback
             && (not axiom_first)
             && not !suppress_clause_axiom_fallback -> (
          match
            Int.incr clause_check_seq_axiom_asked;
            Common.PhaseTime.with_phase "seq-axiom" (fun () ->
                Z3Smt.Z3interface.with_seq_axiom_fallback
                  ~caller_timeout:timeout ~id fenv phi `Timeout)
          with
          | `Valid ->
              Debug.print @@ lazy "[clause check] undecided; proved valid by the sequence axioms";
              `Unsat
          | _ -> res)
      | _ -> res
    in
    (* [questions.clause_check.cvc5_retry_ms]: an undecided question asked of cvc5 as
       the validity of [phi]; only its [unsat] is read *)
    let res =
      match (res, config.questions.clause_check.cvc5_retry_ms) with
      | (`Timeout | `Unknown _), Some ms when ms > 0 ->
          incr cvc5_retry_asked;
          let t0 = Common.PhaseTime.now () in
          let proved =
            PCSatCommon.ValidityAsk.proved_by_cvc5
              {
                ms = cap_ms ms;
                rlimit = None;
                site = "validation";
                phase = "cvc5-retry";
              }
              ~id fenv phi
          in
          if !Common.PhaseTime.on then
            Common.PhaseTime.add
              ("validation-q/cvc5-retry/"
              ^ if proved then "proved" else "not-proved")
              (Common.PhaseTime.now () -. t0);
          if proved then (
            incr cvc5_retry_proved;
            Debug.print @@ lazy "[clause check] undecided; proved valid by cvc5";
            `Unsat)
          else res
      | _ -> res
    in
    (* A constant array is empty data for a learner that reads what the array
       holds, and a clause satisfied by any array makes a solver return one.
       Asking again with the array required to differ at two concrete indices
       is quantifier-free, so it introduces no query shape that might fail to
       return, and the first model is kept whenever the second query does not
       answer [Sat] -- it is a genuine counterexample and this is a preference
       about which one. *)
    let res =
      (* The re-ask conjoins a quantifier-free condition, but the query it is
         conjoined to may itself be quantified -- a clause whose body reads an
         array under a [forall] -- and then the combined query can fail to
         return where the first one did: a 0.1 s refutation became a timeout
         on every run.  The first model is a genuine counterexample, so a
         quantified query simply keeps it. *)
      (* only a sequence re-ask looks through a vacuous binder: the array
         side's gate is kept exactly as it was measured *)
      let neg_phi_seq, arrays_ok, sequences_ok =
        Common.PhaseTime.with_phase "diversify-test" @@ fun () ->
        let neg_phi_seq =
          if config.examples.diversify.sequences then
            Evaluator.simplify (drop_vacuous_binders neg_phi)
          else neg_phi
        in
        let arrays_ok =
          config.examples.diversify.arrays && Formula.is_quantifier_free neg_phi
        in
        let sequences_ok =
          config.examples.diversify.sequences && Formula.is_quantifier_free neg_phi_seq
        in
        (neg_phi_seq, arrays_ok, sequences_ok)
      in
      if not (arrays_ok || sequences_ok) then res
      else
        match res with
        | `Sat model ->
            let constant_arrays =
              if not arrays_ok then []
              else
              List.filter_map model ~f:(fun ((x, srt), v) ->
                  match (srt, v) with
                  | T_array.SArray _, Some t
                    when not (CellQual.array_varies (Evaluator.simplify_term t)) ->
                      Some (x, srt)
                  | _ -> None)
            in
            (* a sequence the model left empty, or gave one element, or one
               element repeated: the cells read off it cannot tell positions
               apart *)
            let uninformative_sequences =
              if not sequences_ok then []
              else
                List.filter_map model ~f:(fun ((x, srt), v) ->
                    match (srt, v) with
                    | T_seq.SSeq se, Some t
                      when CellArray.sequence_lacks_variety (Evaluator.simplify_term t) ->
                        Some (x, srt, se)
                    | _ -> None)
            in
            if List.is_empty constant_arrays && List.is_empty uninformative_sequences
            then res
            else
              (* Any model of [neg_phi] is a counterexample, so conjoining a
                 preference and keeping the first model when the preference
                 cannot be met only chooses WHICH counterexample is used; it
                 cannot make the verdict wrong. *)
              let vary_sequences =
                List.map uninformative_sequences ~f:(fun (x, srt, se) ->
                    CellArray.sequence_vary_condition ~elem_sort:se
                      ~read_indices:(CellArray.seq_read_indices neg_phi_seq x)
                      (Term.mk_var x srt))
              in
              let vary =
                Formula.and_of @@ (fun arrays -> arrays @ vary_sequences)
                @@ List.map constant_arrays ~f:(fun (x, srt) ->
                       let a = Term.mk_var x srt in
                       match CellQual.uncurry_array_sort srt with
                       | [ si ], se
                         when Term.is_int_sort si
                              && config.examples.diversify.at_clause_read_indices
                              && List.length (CellQual.clause_read_indices neg_phi x) >= 2 ->
                           let idxs = List.take (CellQual.clause_read_indices neg_phi x) 6 in
                           let rec pairs = function
                             | [] -> []
                             | t :: rest -> List.map rest ~f:(fun u -> (t, u)) @ pairs rest
                           in
                           Formula.or_of
                           @@ List.map (pairs idxs) ~f:(fun (t, u) ->
                                  Formula.neq
                                    (T_array.mk_select si se a t)
                                    (T_array.mk_select si se a u))
                       | [ si ], se when Term.is_int_sort si ->
                           (* the integer case as it was measured: two fixed
                              indices, a quantifier-free query *)
                           Formula.neq
                             (T_array.mk_select si se a (T_int.zero ()))
                             (T_array.mk_select si se a (T_int.one ()))
                       | index_sorts, elem_sort ->
                           (* any other index -- a quantified sort, an
                              enumeration, or a curried chain -- has no two
                              indices to name, so the query asks for two index
                              TUPLES at which the array differs, bound
                              existentially so that the model returned is
                              still about the clause's own variables *)
                           let tuple () =
                             List.map index_sorts ~f:(fun si ->
                                 (Ident.mk_fresh_tvar (), si))
                           in
                           let t1 = tuple () and t2 = tuple () in
                           let read tup =
                             CellQual.select_chain_old ~index_sorts ~elem_sort a
                               (List.map tup ~f:(fun (i, si) -> Term.mk_var i si))
                           in
                           Formula.exists (t1 @ t2)
                             (Formula.neq (read t1) (read t2)))
              in
              Debug.print
              @@ lazy
                   (sprintf
                      "the counterexample's array is constant at %d place(s) and its sequence uninformative at %d; asking again for one that varies"
                      (List.length constant_arrays)
                      (List.length uninformative_sequences));
              (match
                 Z3Smt.Z3interface.check_sat ~id ~timeout fenv
                   [ Formula.mk_and (if sequences_ok then neg_phi_seq else neg_phi) vary ]
               with
              | `Sat model' -> `Sat model'
              | _ -> res)
        | _ -> res
    in
    (* [examples.diversify.arms]: a counterexample in the same arm of a
       recurring disjunction of the query as the last one is asked again in
       the other arms; the first model is kept unless one of them answers
       [Sat], so this only chooses which counterexample is used *)
    let res =
      match res with
      | `Sat model
        when config.examples.diversify.arms && (not verdict_only)
             && not (Z3Smt.Z3interface.may_not_return neg_phi) ->
          Common.PhaseTime.with_phase "diversify-arms" @@ fun () ->
          `Sat
            (PCSatCommon.ArmRotation.reask
               ~ask:(fun psi ->
                 match Z3Smt.Z3interface.check_sat ~id ~timeout fenv [ psi ] with
                 | `Sat m -> Some m
                 | _ -> None)
               neg_phi model)
      | _ -> res
    in
    (* [examples.diversify.scalars]: a counterexample whose integers lie
       close to the last one asked for the same variables is asked again with
       a Manhattan distance required; the first model is kept unless the
       second query answers [Sat], so this only chooses which counterexample
       is used.  Not asked for a verdict-only caller (it reads no model), nor
       on a shape [may_not_return] refuses. *)
    let res =
      match res with
      | `Sat model
        when config.examples.diversify.scalars && (not verdict_only)
             && (not (List.is_empty model))
             && not (Z3Smt.Z3interface.may_not_return neg_phi) ->
          Common.PhaseTime.with_phase "diversify-scalars" @@ fun () ->
          `Sat
            (PCSatCommon.ScalarDiversity.reask
               ~ask:(fun psi ->
                 match Z3Smt.Z3interface.check_sat ~id ~timeout fenv [ psi ] with
                 | `Sat m -> Some m
                 | _ -> None)
               neg_phi model)
      | _ -> res
    in
    (* [examples.diversify.rationals]: a counterexample's real values of large
       denominator are replaced by simpler ones that keep the query true, and
       the query asked again with them pinned; the first model is kept unless
       the pinned query answers [Sat], so this only chooses which
       counterexample is used *)
    let res =
      match (res, config.examples.diversify.rationals) with
      | `Sat model, Some max_den
        when (not verdict_only) && (not (List.is_empty model))
             && not (Z3Smt.Z3interface.may_not_return neg_phi) ->
          Common.PhaseTime.with_phase "diversify-rationals" @@ fun () ->
          `Sat
            (PCSatCommon.SimpleRationals.reask ~max_den
               ~ask:(fun psi ->
                 match Z3Smt.Z3interface.check_sat ~id ~timeout fenv [ psi ] with
                 | `Sat m -> Some m
                 | _ -> None)
               neg_phi model)
      | _ -> res
    in
    (match (res, witness_vars) with
    | _, [] -> ()
    | `Sat model, _ ->
        List.iter model ~f:(fun ((x, _s), v) ->
            match v with
            | Some t when List.Assoc.mem witness_vars ~equal:Stdlib.( = ) x -> (
                match Term.value_of (Evaluator.simplify_term t) with
                | Value.Int z ->
                    if config.examples.record.cell_witnesses then CellQual.record_witness z
                | _ -> ()
                | exception exn_ when not (Common.Timer.is_async exn_) -> ())
            | _ -> ())
    | _ -> ());
    res

  (* The budget of a validation query over [phi], the clause with the candidate
     substituted: [questions.quantified_timeout_ms] where [phi] still contains a
     quantifier or applies a recursive known function (the smaller of the two
     when both are set), [questions.timeout_ms] otherwise.  A recursive definition is a
     universal axiom the solver instantiates lazily, so a question applying
     one is quantified in all but syntax: a quantifier-free validation
     question over a list's recursive [length], whose refutation needs
     [length x >= 0] by induction, did not return in 30 s standalone nor
     before a 60 s kill in process, while the 55 such questions of the same
     run that were decided took at most 0.21 s each.  A question cut by the
     budget is undecided, which rejects the candidate and is never a wrong
     answer.  The functions are read from the process-global environment,
     which holds every definition the input declares; an over-approximation
     only gives a question this budget. *)
  let timeout_for phi =
    if
      Formula.is_quantifier_free phi
      && not (Z3Smt.Z3interface.applies_recursive_function (LogicOld.get_fenv ()) phi)
    then config.questions.timeout_ms
    else
      match (config.questions.timeout_ms, config.questions.quantified_timeout_ms) with
      | Some a, Some b ->
          (* counted so that a run shows the quantified budget was applied;
             changes nothing *)
          if b < a then Common.PhaseTime.event_here "smt-timeout-quantified";
          Some (min a b)
      | None, q ->
          if Option.is_some q then
            Common.PhaseTime.event_here "smt-timeout-quantified";
          q
      | t, None -> t

  (* The counterexample question for a clause [phi] that reads a sequence
     under a quantifier, asked through [SeqInstantiation.decide_clause]: first
     its instantiated forms, each implying [phi], whose validity ends the
     check; then, for a candidate they do not prove, [phi]'s negation with its
     free variables fixed to a refuted form's model, and with each free
     sequence a literal of a small length; and only when none of those finds a
     counterexample, the unrewritten question, under a budget when none is
     set.  A refuted form's model is never a counterexample by itself -- the
     form is stronger than [phi] -- and only a model of [phi]'s own negation is
     returned. *)
  (* [true] exactly while one question runs under [houdini.questions.seq_question_ms]:
     the asks of [check_clause_readback] then stop the route once the
     narrowed deadline is spent ([Question_budget_spent]) *)
  let in_capped_question = ref false

  (* [true] exactly while [houdini_fixed_point] runs: [houdini.questions.seq_question_ms]
     caps its questions only, never the final check's, where a question cut
     short would reject the whole fixed point and send the pre-pass into
     another round instead of dropping one atom *)
  let in_houdini_fixed_point = houdini_window.in_fixed_point

  (* [true] exactly while a per-atom question of [houdini_fixed_point] is
     asked (not a conjunction question of [houdini.questions.drop_by_model], not the
     final check), for [houdini.questions.atom_questions_prove_only] *)
  let in_houdini_atom_question = houdini_window.in_atom_question

  (* [true] exactly while a conjunction question of [houdini.questions.drop_by_model]
     is asked, for [houdini.questions.drop_by_model.conjunction_ms] *)
  let in_houdini_conjunction_question = houdini_window.in_conjunction_question

  exception Question_budget_spent

  (* raised from an ask of the read-back route when the question's own budget
     is spent; outside a capped question it never fires *)
  let stop_if_question_spent () =
    if !in_capped_question && houdini_budget_spent () then
      raise Question_budget_spent

  let check_clause_readback ?(guard_both_ways = true) ?(ladder = false)
      ~timeout fenv phi =
    let ask_form form =
      stop_if_question_spent ();
      if Z3Smt.Z3interface.may_not_return form then `Undecided
      else
        let started = Common.Clock.now_float () in
        let res =
          Z3Smt.Z3interface.check_sat ~id ~timeout:(cap_timeout readback_instance_timeout)
            fenv
            [ Formula.nnf_of (Formula.negate form) ]
        in
        Debug.print
        @@ lazy
             (sprintf "[read-back instance] %s in %.3f s: %s"
                (match res with
                | `Unsat -> "valid"
                | `Sat _ -> "not valid"
                | _ -> "undecided")
                (elapsed_since started) (Formula.str_of form));
        match res with
        | `Unsat -> `Valid
        | `Sat model -> `Invalid model
        | _ when config.questions.readback.retry_undecided_forms -> (
            (* the same question under an explicit tactic of equivalences:
               only its [unsat] is read, so this can only prove the form *)
            let started = Common.Clock.now_float () in
            let res =
              try
                Z3Smt.Z3interface.check_sat_by_elimination
                  ~timeout:(cap_ms readback_retry_timeout) ~id fenv
                  [ Formula.nnf_of (Formula.negate form) ]
              with e when not (Common.Timer.is_async e) ->
                `Unknown (Exn.to_string e)
            in
            Debug.print
            @@ lazy
                 (sprintf "[read-back instance retry] %s in %.3f s"
                    (match res with `Unsat -> "valid" | _ -> "undecided")
                    (elapsed_since started));
            match res with `Unsat -> `Valid | _ -> `Undecided)
        | _ -> `Undecided
    in
    (* A clause whose read-back candidate occurs both in a premise and in the
       conclusion binds positions both ways once in negation normal form.
       Its unrewritten question did not return, its budget notwithstanding
       (observed on a composition clause over three sequences: still running
       at the 120 s limit under a 10 s budget), and a solver call cannot be
       interrupted here, so it is not asked; the refutations below still
       look for a counterexample.  Not asking can only leave the check
       undecided, never decide it wrongly. *)
    let binds_both_ways =
      let rec binders ~pos phi =
        match phi with
        | Formula.Bind (b, _, body, _) ->
            let here =
              match (b, pos) with
              | Formula.Forall, true | Formula.Exists, false -> [ `Forall ]
              | Formula.Exists, true | Formula.Forall, false -> [ `Exists ]
              | _ -> []
            in
            here @ binders ~pos body
        | Formula.UnaryOp (Formula.Not, p, _) -> binders ~pos:(not pos) p
        | Formula.BinaryOp ((Formula.And | Formula.Or), p, q, _) ->
            binders ~pos p @ binders ~pos q
        | Formula.BinaryOp (Formula.Imply, p, q, _) ->
            binders ~pos:(not pos) p @ binders ~pos q
        | _ -> []
      in
      let bs = binders ~pos:true phi in
      List.mem bs `Forall ~equal:Stdlib.( = )
      && List.mem bs `Exists ~equal:Stdlib.( = )
    in
    let ask_full () =
      stop_if_question_spent ();
      if guard_both_ways && binds_both_ways then (
        Debug.print
        @@ lazy "[read-back full question] not asked: binds both ways";
        `Unknown "not asked")
      else
      let started = Common.Clock.now_float () in
      let res =
        check_clause_nonparam_smt
          ~timeout:
            (match timeout with None -> readback_full_timeout | t -> t)
          fenv phi
      in
      Debug.print
      @@ lazy
           (sprintf "[read-back full question] %s in %.3f s"
              (match res with
              | `Unsat -> "valid"
              | `Sat _ -> "counterexample"
              | _ -> "undecided")
              (elapsed_since started));
      res
    in
    let ask_pinned model =
      stop_if_question_spent ();
      let free = Formula.tvs_of phi in
      let pins =
        List.filter_map model ~f:(fun ((x, srt), v) ->
            match v with
            | Some t when Set.mem free x -> Some (Formula.eq (Term.mk_var x srt) t)
            | _ -> None)
      in
      if List.is_empty pins then `Unknown "nothing to pin"
      else
        let neg_phi = Evaluator.simplify @@ Formula.mk_neg phi in
        let neg_phi =
          if config.questions.rewrites.split_seq_reads then
            Evaluator.rewrite_seq_read_over_concat neg_phi
          else neg_phi
        in
        let started = Common.Clock.now_float () in
        let res =
          Z3Smt.Z3interface.check_sat ~id ~timeout:(cap_timeout readback_pinned_timeout) fenv
            [ Formula.and_of (neg_phi :: pins) ]
        in
        Debug.print
        @@ lazy
             (sprintf "[read-back pinned] %s in %.3f s"
                (match res with
                | `Unsat -> "no counterexample there"
                | `Sat _ -> "counterexample"
                | _ -> "undecided")
                (elapsed_since started));
        res
    in
    (* the negation with every free sequence a literal of a small length:
       a model of it is a model of the negation, and fixing the length turns
       each read under the cell universal into a case split over positions *)
    let bounded =
      List.map SeqPin.lengths ~f:(fun length () ->
          stop_if_question_spent ();
          match SeqPin.strengthened_negation ~length [ phi ] with
          | None -> `Unknown "no free sequence"
          | Some neg ->
              let started = Common.Clock.now_float () in
              let res =
                Z3Smt.Z3interface.check_sat ~id
                  ~timeout:(cap_timeout readback_pinned_timeout) fenv [ neg ]
              in
              Debug.print
              @@ lazy
                   (sprintf "[read-back length %d] %s in %.3f s" length
                      (match res with
                      | `Unsat -> "no counterexample there"
                      | `Sat _ -> "counterexample"
                      | _ -> "undecided")
                      (elapsed_since started));
              res)
    in
    (* With [ladder], the unrewritten question is preceded by the
       zero-unknown verdict's instantiation ladder ([SeqInstantiation.
       prove_valid], with the switches its caller set): every form it asks
       implies its piece of [phi], so its [`Valid] proves [phi], and
       anything else falls through to the question asked without it.  It is
       asked after the refuters, so a [phi] with a cheap counterexample does
       not pay for it. *)
    let ask_full =
      if not ladder then ask_full
      else fun () ->
        stop_if_question_spent ();
        let rw =
          if !SeqInstantiation.onepoint_split_forms then
            Evaluator.elim_onepoint_and_split_binders
          else Fn.id
        in
        let started = Common.Clock.now_float () in
        let res =
          SeqInstantiation.prove_valid ~enabled:true
            ~already_valid:(fun _ -> false)
            ~ask:(fun form -> ask_form (rw form))
            [ rw phi ]
        in
        Debug.print
        @@ lazy
             (sprintf "[read-back ladder] %s in %.3f s"
                (match res with `Valid -> "valid" | `Undecided -> "undecided")
                (elapsed_since started));
        match res with `Valid -> `Unsat | `Undecided -> ask_full ()
    in
    (* [houdini.questions.atom_questions_prove_only]: a per-atom question of the
       pre-pass's fixed point keeps its atom only when proved, a refutation
       and an undecided answer both dropping it, so its refuters are not
       built: building one length-bounded refuter is not a solver call and is
       cut short by no budget (6 and 8.5 s on two such questions) *)
    let prove_only =
      config.houdini.questions.atom_questions_prove_only && !in_houdini_atom_question
    in
    SeqInstantiation.decide_clause
      ~subst_definitions:config.questions.readback.subst_definitions ~ask_form ~ask_full
      ~ask_pinned:
        (if prove_only then fun _ -> `Unknown "refuters not built"
         else ask_pinned)
      ~bounded:(if prove_only then [] else bounded)
      phi

  let binds_sequence_existentially =
    HoudiniCandidates.binds_sequence_existentially
      ~arrays:config.houdini.questions.array_existentials

  (* [true] exactly while [houdini_outcome] runs (the fixed point and its
     final check) with [houdini.questions.seq_instantiation] on *)
  let in_houdini_seq_instantiation = houdini_window.in_seq_instantiation

  (* the sequence-existential questions asked first as plain questions under
     [houdini.questions.seq_plain_first_ms], and how many of them that decided (asked,
     decided); never reset here, read by the tests *)
  let houdini_plain_first_counts = (ref 0, ref 0)

  (* the sequence-existential questions that ran under
     [houdini.questions.seq_question_ms] and how many of them its budget cut short
     (asked, cut); never reset here, read by the tests *)
  let houdini_question_cap_counts = (ref 0, ref 0)

  (* [f ()] with the pre-pass's deadline narrowed to [ms] from now (never
     widened) and restored afterwards, its [Question_budget_spent] answered
     [`Timeout]; [f ()] itself when [ms] is [None] *)
  let within_question_budget ms f =
    match ms with
    | None -> f ()
    | Some _ when not !in_houdini_fixed_point -> f ()
    | Some ms ->
        let saved = !houdini_deadline in
        let saved_capped = !in_capped_question in
        let mine = Time_ns.add (Common.Clock.now_ns ()) (Time_ns.Span.of_int_ms ms) in
        houdini_deadline :=
          Some
            (match saved with
            | Some d when Time_ns.( < ) d mine -> d
            | _ -> mine);
        in_capped_question := true;
        incr (fst houdini_question_cap_counts);
        Exn.protect
          ~finally:(fun () ->
            houdini_deadline := saved;
            in_capped_question := saved_capped)
          ~f:(fun () ->
            try f ()
            with Question_budget_spent ->
              incr (snd houdini_question_cap_counts);
              Debug.print
              @@ lazy
                   (sprintf
                      "[houdini] sequence-existential question: its %d ms \
                       spent, left undecided"
                      ms);
              `Timeout)

  (* The counterexample question for a clause [phi].  Outside the pre-pass,
     and inside it without [houdini.questions.seq_instantiation], exactly as before.
     Inside it with the switch, a question that binds a sequence
     existentially goes through [check_clause_readback] with the
     zero-unknown verdict's ladder asked after the refuters and its
     unrewritten question always asked last (the guard against a question
     binding both ways is the read-back route's own, and the plain route
     never had it), so its answer is valid only when an instantiated form or
     that question proves it, and a counterexample only when it is a model
     of [phi]'s negation. *)
  (* [verdict_only] as for [check_clause_nonparam_smt], on the route that
     asks the plain question; the read-back routes ignore it *)
  (* [houdini.questions.mode] other than [Plain_first]: a sequence-existential
     question of the pre-pass's fixed point asked by two searches, within the
     question's cap (the pre-pass's deadline, narrowed by
     [houdini.questions.seq_question_ms], or [houdini.questions.drop_by_model.conjunction_ms] for
     a conjunction question, as without the field):
     - the plain question ([plain]): the question itself, asked of the solver
       for a slice;
     - the route ([route]): the witness-instantiation route, in a forked copy
       killed at the end of its slice, asked for a proof only.
     [Switch] asks the plain question for [houdini.questions.seq_plain_first_ms] (the
     whole cap when that is unset), then the route for the rest; [Dovetail]
     alternates them in slices doubling from [houdini.questions.mode.start_ms];
     [Race] runs both at once in two copies and kills the loser.  The result
     is the first decisive answer, or [`Timeout] once the cap is spent.

     Soundness, answer by answer: [`Unsat] from the plain question is the
     question's own validity; [`Sat m] from it is a model of the question's
     negation, so a countermodel of the question; the route's forms each imply
     the question, so a form proved valid proves it, and the route answers
     [`Unsat] only then -- any other outcome of a route slice (a refuter's
     model, which does not come back from a copy, undecided, killed) is no
     answer, never a refutation.  So the answers are those the two searches
     give alone; which one answers first, and when, is all the mode decides.

     Why: one search first and then the other guesses which kind of answer a
     question has, and each guess lost a file -- a conjunction the plain
     question refutes in under 1.5 s waited 10 s for the route, and one the
     route proves in 2-5.5 s was cut short when the plain question kept it.
     The route runs in a killed copy because building its forms is not a
     solver call and nothing else bounds it. *)
  (* Measurement only (COAR_SEQINST_TIMING, COAR_HSHARE_COMPARE): the pass and
     clause of the pre-pass's fixed point being asked, and the clause's
     premise part under the current candidate (the question without its head
     atom), so that the instantiation timings can be attributed to a clause
     and compared with what the premise alone costs.  No answer reads them. *)
  let houdini_instr_pass = houdini_window.instr_pass
  let houdini_instr_clause = houdini_window.instr_clause
  let houdini_instr_question = ref 0
  let houdini_instr_premise = houdini_window.instr_premise

  let houdini_instr_compare =
    match Sys.getenv "COAR_HSHARE_COMPARE" with
    | None | Some "" -> false
    | Some _ -> true

  (* the seconds [SeqInstantiation.instantiate] takes over the pieces of
     [phi] as the ladder splits it, the number of pieces, and the ground
     sequence terms of [phi] *)
  let houdini_instr_instantiate phi =
    let nnf = Evaluator.simplify (Formula.nnf_of phi) in
    let ps = SeqInstantiation.pieces nnf in
    let t0 = Common.Clock.now_s () in
    List.iter ps ~f:(fun piece ->
        ignore
          (SeqInstantiation.instantiate ?max_nodes:!SeqInstantiation.piece_max_nodes
             (SeqInstantiation.prepare_piece piece)
            : Formula.t));
    ( Common.Clock.now_s () -. t0,
      List.length ps,
      Set.Poly.of_list
        (SeqInstantiation.ground_sequences ~free:(Formula.tvs_of nnf) nnf) )

  let houdini_instr_note phi =
    if Option.is_some SeqInstantiation.instr_file then (
      Int.incr houdini_instr_question;
      SeqInstantiation.instr_tag :=
        sprintf "p%d\tc%d\tq%d" !houdini_instr_pass !houdini_instr_clause
          !houdini_instr_question;
      SeqInstantiation.instr_line
        (sprintf "question\tsize=%d\thash=%d" (Formula.ast_size phi)
           (String.hash (Formula.str_of phi)));
      match !houdini_instr_premise with
      | Some premise when houdini_instr_compare ->
          let tag = !SeqInstantiation.instr_tag in
          SeqInstantiation.instr_tag := tag ^ "\tcmp-question";
          let qs, qn, qpool = houdini_instr_instantiate phi in
          let premise = Evaluator.simplify (Lazy.force premise) in
          SeqInstantiation.instr_tag := tag ^ "\tcmp-premise";
          let ps, pn, ppool = houdini_instr_instantiate premise in
          SeqInstantiation.instr_tag := tag;
          SeqInstantiation.instr_line
            (sprintf
               "cmp\tq_secs=%.4f\tp_secs=%.4f\tq_pieces=%d\tp_pieces=%d\tq_pool=%d\tp_pool=%d\tnew_in_q=%d\tpremise_hash=%d"
               qs ps qn pn (Set.length qpool) (Set.length ppool)
               (Set.length (Set.diff qpool ppool))
               (String.hash (Formula.str_of premise)))
      | _ -> ())

  let houdini_question_counts = (ref 0, ref 0, ref 0)
  (* questions asked, decided by the plain question, proved by the route;
     never reset here, read by the tests *)

  let houdini_two_searches ~timeout ~verdict_only fenv phi =
    let asked, by_plain, by_route = houdini_question_counts in
    incr asked;
    within_question_budget
      (match (HoudiniConfig.Switch.drop_by_model_conjunction_ms config.houdini) with
      | Some ms when !in_houdini_conjunction_question -> Some ms
      | _ -> config.houdini.questions.seq_question_ms)
      (fun () ->
        let started = Common.Clock.now_ns () in
        (* the time left for the question; with no deadline at all, the
           caller's [timeout], or 64 s *)
        let left () =
          match houdini_remaining_ms () with
          | Some r -> r
          | None ->
              Option.value timeout ~default:64000
              - Time_ns.Span.to_int_ms (Time_ns.diff (Common.Clock.now_ns ()) started)
        in
        let slice t = Int.max 1 (Int.min t (left ())) in
        let plain ms =
          match
            Common.PhaseTime.with_phase "plain" (fun () ->
                check_clause_nonparam_smt ~timeout:(Some ms) ~verdict_only fenv
                  phi)
          with
          | (`Unsat | `Sat _) as r ->
              incr by_plain;
              Some r
          | _ -> None
        in
        (* the route as a proof search, in the process that runs it: no deadline
           of the pre-pass is read there (a copy is killed instead), so it asks
           no further forked copy *)
        let route_proves () =
          houdini_deadline := None;
          match
            check_clause_readback ~guard_both_ways:false ~ladder:true
              ~timeout:None fenv phi
          with
          | `Unsat -> `Proved
          | _ -> `Not_proved
        in
        let route ms =
          houdini_instr_note phi;
          match
            Common.PhaseTime.with_phase "route" (fun () ->
                PCSatCommon.ForkedQuery.run ~ms route_proves)
          with
          | Some `Proved ->
              incr by_route;
              Some `Unsat
          | _ -> None
        in
        let decided r = Option.value r ~default:`Timeout in
        match config.houdini.questions.mode with
        | HoudiniConfig.Plain_first -> assert false
        | Switch -> (
            let first =
              match config.houdini.questions.seq_plain_first_ms with
              | Some ms -> slice ms
              | None -> slice Int.max_value
            in
            match plain first with
            | Some r -> r
            | None -> if left () <= 0 then `Timeout else decided (route (slice Int.max_value)))
        | Dovetail { start_ms } ->
            let rec go t =
              if left () <= 0 then `Timeout
              else
                match plain (slice t) with
                | Some r -> r
                | None -> (
                    if left () <= 0 then `Timeout
                    else
                      match route (slice t) with
                      | Some r -> r
                      | None -> go (2 * t))
            in
            go (Int.max 1 start_ms)
        | Race -> (
            (* both searches in copies; the plain copy answers its verdict
               only (a model does not come back), and a refutation is then
               asked again here for its countermodel *)
            let ms = slice Int.max_value in
            match
              Common.PhaseTime.with_phase "race" (fun () ->
                  PCSatCommon.ForkedQuery.race ~ms
                    ~decisive:(function `Proved | `Refuted -> true | _ -> false)
                    [
                      (fun () ->
                        houdini_deadline := None;
                        match
                          check_clause_nonparam_smt ~timeout:(Some ms)
                            ~verdict_only:true fenv phi
                        with
                        | `Unsat -> `Proved
                        | `Sat _ -> `Refuted
                        | _ -> `Undecided);
                      (fun () ->
                        match route_proves () with
                        | `Proved -> `Proved
                        | `Not_proved -> `Undecided);
                    ])
            with
            | Some `Proved ->
                incr by_route;
                `Unsat
            | Some `Refuted -> (
                incr by_plain;
                if verdict_only then `Sat []
                else
                  match
                    check_clause_nonparam_smt ~timeout:(Some (slice ms))
                      ~verdict_only fenv phi
                  with
                  | `Sat m -> `Sat m
                  | _ -> `Sat [])
            | _ -> `Timeout))

  let check_clause_nonparam_uncached ?(timeout = None) ?(verdict_only = false)
      fenv phi =
    if
      config.questions.readback.instantiate_universals
      && (not (Formula.is_quantifier_free phi))
      && reads_sequence phi
    then
      Common.PhaseTime.with_phase "readback" (fun () ->
          check_clause_readback ~timeout fenv phi)
    else if
      !in_houdini_seq_instantiation
      && !in_houdini_fixed_point
      && (match config.houdini.questions.mode with
         | HoudiniConfig.Plain_first -> false
         | _ -> true)
      && binds_sequence_existentially phi
    then
      Common.PhaseTime.with_phase "question-mode" (fun () ->
          houdini_two_searches ~timeout ~verdict_only fenv phi)
    else if !in_houdini_seq_instantiation && binds_sequence_existentially phi
    then
      let plain =
        match
          match (HoudiniConfig.Switch.conjunction_plain_first_ms config.houdini) with
          | Some ms when !in_houdini_conjunction_question -> Some ms
          | _ -> config.houdini.questions.seq_plain_first_ms
        with
        | None -> None
        | Some ms -> (
            let t =
              match timeout with Some t when t < ms -> Some t | _ -> Some ms
            in
            incr (fst houdini_plain_first_counts);
            match
              Common.PhaseTime.with_phase "plain-first" (fun () ->
                  check_clause_nonparam_smt ~timeout:t ~verdict_only fenv phi)
            with
            | (`Unsat | `Sat _) as r ->
                incr (snd houdini_plain_first_counts);
                Debug.print
                @@ lazy
                     "[houdini] sequence-existential question: decided by the \
                      plain question";
                Some r
            | _ -> None)
      in
      match plain with
      | Some r -> r
      | None ->
          Debug.print
          @@ lazy
               "[houdini] sequence-existential question: witness instantiation";
          houdini_instr_note phi;
          Common.PhaseTime.with_phase "readback-ladder" (fun () ->
              within_question_budget
                (match (HoudiniConfig.Switch.drop_by_model_conjunction_ms config.houdini) with
                | Some ms when !in_houdini_conjunction_question -> Some ms
                | _ -> config.houdini.questions.seq_question_ms)
                (fun () ->
                  let route () =
                    check_clause_readback ~guard_both_ways:false ~ladder:true
                      ~timeout fenv phi
                  in
                  (* [houdini.questions.atom_questions_prove_only]: a per-atom question
                     needs only whether the route proves it, so the route runs
                     in a forked copy killed when the deadline is reached,
                     which bounds the building of its forms too *)
                  match houdini_remaining_ms () with
                  | Some r
                    when config.houdini.questions.atom_questions_prove_only
                         && !in_houdini_atom_question -> (
                      match
                        PCSatCommon.ForkedQuery.run ~ms:(max 1 r) (fun () ->
                            match route () with
                            | `Unsat -> `Proved
                            | _ -> `Not_proved)
                      with
                      | Some `Proved -> `Unsat
                      | Some `Not_proved -> `Unknown "not proved by the route"
                      | None -> `Timeout)
                  | _ -> route ()))
    else check_clause_nonparam_smt ~timeout ~verdict_only fenv phi

  (* [houdini.questions.memo.questions]: the decided answers of the pre-pass's
     questions, keyed by [verdict_only] and the question itself (compared
     structurally, hashed deeply), for the pre-pass whose deadline is the
     first component (a new pre-pass, or none, starts afresh).  The key is
     not the printed question: printing every question to look it up was
     about a third of the pre-pass's own CPU time on a fold loop, and the
     printed form leaves out a variable's sort, so it could make two
     different questions one key *)
  let houdini_memo :
      (Time_ns.t option
      * (bool * Formula.t, [ `Unsat | `Sat of _ ]) Hashtbl.t)
      ref =
    ref (None, Hashtbl.PolyDeep.create ())

  let houdini_memo_hits = ref 0

  (* With [houdini.questions.memo.questions], inside the pre-pass (its deadline set),
     a question equal to one already decided in the same pre-pass,
     with the same [verdict_only], gets that answer without being asked: the
     problem and its definitions do not change inside one pre-pass, so the
     same formula has the same validity, and only a decided answer ([`Unsat],
     or [`Sat] with its model) is kept, never an undecided one, which a second
     asking might decide.  Outside the pre-pass, or with the field off, every
     question is asked. *)
  let check_clause_nonparam ?(timeout = None) ?(verdict_only = false) fenv phi
      =
    match !houdini_deadline with
    | Some _ as deadline when config.houdini.questions.memo.questions ->
        let tbl =
          match !houdini_memo with
          | d, tbl when Option.equal Time_ns.equal d deadline -> tbl
          | _ ->
              let tbl = Hashtbl.PolyDeep.create () in
              houdini_memo := (deadline, tbl);
              tbl
        in
        let key = (verdict_only, phi) in
        (match Hashtbl.find tbl key with
        | Some r ->
            incr houdini_memo_hits;
            Debug.print @@ lazy "[houdini] question answered as before";
            (r :> [ `Unsat | `Sat of _ | `Timeout | `Unknown of string ])
        | None -> (
            match check_clause_nonparam_uncached ~timeout ~verdict_only fenv phi with
            | `Unsat -> Hashtbl.set tbl ~key ~data:`Unsat; `Unsat
            | `Sat m -> Hashtbl.set tbl ~key ~data:(`Sat m); `Sat m
            | r -> r))
    | _ -> check_clause_nonparam_uncached ~timeout ~verdict_only fenv phi

  (* The parameter values under which [check_clause_param_smt] found its
     clause group valid, for the candidate being validated; reset by
     [find_all_counterexamples].  The groups share no parameter, so the
     values of different groups never conflict. *)
  let param_values : (Ident.tvar, Logic.term) Map.Poly.t ref =
    ref Map.Poly.empty

  (* [`Unsat] (no counterexample) only when some values of the parameters
     make [phi] valid; those values are recorded in [param_values], since a
     parametric candidate is a solution only under them. *)
  let check_clause_param_smt ?(timeout = None) fenv params_senv uni_senv phi =
    let qphi =
      Formula.forall
        (Map.Poly.to_alist @@ Logic.to_old_sort_env_map uni_senv)
        phi
    in
    let timeout = cap_timeout timeout in
    match Z3Smt.Z3interface.check_sat ~id ~timeout fenv [ qphi ] with
    | `Sat model ->
        List.iter (LogicOld.remove_dontcare model) ~f:(fun (x, t) ->
            if Map.Poly.mem params_senv x then
              param_values :=
                Map.Poly.set !param_values ~key:x
                  ~data:(Logic.ExtTerm.of_old_term t));
        `Unsat
    | _ ->
        (* unsat, unknown, timeout*)
        let sub = Logic.to_old_dummies params_senv in
        check_clause_nonparam_smt ~timeout fenv (Formula.subst sub phi)

  let solve =
    let module Z3interface =
      Z3Smt.Z3interfaceNew.Make (Z3Smt.Z3interfaceNew.ExtTerm) in
    fun senv phi ->
      Common.PhaseTime.with_phase "fresh-ctx-check" (fun () ->
          Z3interface.check_sat [ phi ] senv (Z3.mk_context []))

  (* Consecutive rounds that rejected the candidate and learnt nothing.  The
     functor is applied once per problem ([make] above), so this counts within
     one solve and is not the shape where per-object state lives in a global. *)
  let fruitless_rounds = ref 0

  (* The candidates of every fruitless round so far, by [candidates_key]: a
     printed form, compared as a string, since a candidate holds sort maps
     whose comparator is a closure and cannot be compared structurally.  Two
     printed forms that agree name the same candidate up to the printer's
     injectivity, which is all a repeat count needs. *)
  let fruitless_keys : string Hash_set.t = Hash_set.create (module String)

  (* the unknowns applied by the problem clauses whose question this round's
     validation left undecided; emptied at the start of every round and handed
     to the synthesis phase through [VersionSpace.undecided_unknowns] when the
     round learnt nothing *)
  let round_undecided_unknowns : Ident.tvar Set.Poly.t ref = ref Set.Poly.empty

  let candidates_key (candidates : (CandSol.t * CandSol.tag) list) =
    String.concat_map_list ~sep:"\n" candidates ~f:(fun (c, _) ->
        CandSol.str_of c)
  let print_log = false

  let check_clause_param_strat_synth ?(timeout = None) fenv params_senv uni_senv
      phi =
    let open StratSynth in
    let f =
      Evaluator.simplify @@ Formula.elim_ite
      @@ Formula.exists
           (Map.Poly.to_alist @@ Logic.to_old_sort_env_map params_senv)
      @@ Formula.forall (Map.Poly.to_alist @@ Logic.to_old_sort_env_map uni_senv)
      @@ Formula.aconv_tvar phi (*ToDo: this is necessary due to a bug?*)
    in
    (*print_endline (sprintf "original input: %s\n" (Formula.str_of f));*)
    match LIA.formula_of_term @@ Logic.ExtTerm.of_old_formula f with
    | None ->
        (* f is possibly non-linear *)
        check_clause_param_smt ~timeout fenv params_senv uni_senv phi
    | Some f -> (
        (*Debug.print @@ lazy (sprintf "input: %s\n" (formula_to_string f));*)
        let p, s = LIAStrategySynthesis.nondet_strategy_synthesis solve f in
        (*Debug.print @@ lazy (sprintf "strategy skelton for %s:\n%s" (player_to_string p) (ssforest_to_string s));*)
        match p with
        | SAT ->
            `Unsat (*ToDo: show model for parameters of the candidate solution*)
        | UNSAT -> (
            let f = PreFormula.neg_formula LIA.neg_atom f in
            let fml, chc, det, params = LIAStrategySynthesis.loseCHC [] s f in
            (*Debug.print @@ lazy "strategy template:";
              Map.Poly.iteri det ~f:(fun ~key ~data:(senv, t) ->
              Debug.print @@ lazy
              (sprintf "%s: %s" (Ident.name_of_tvar key)
                (Logic.ExtTerm.str_of_term
                  (Map.force_merge (Map.Poly.of_alist_exn params) senv) t)));
              Debug.print @@ lazy "";*)
            let chc =
              ( Map.Poly.empty,
                Logic.ExtTerm.imply_of fml (Logic.BoolTerm.mk_bool false) )
              :: chc
            in
            let problem =
              PCSP.Problem.of_formulas
                ~params:(PCSP.Params.make @@ Map.of_list_exn params)
              @@ Set.Poly.of_list chc
            in
            if print_log then (
              Debug.print
              @@ lazy "recursion-free CHC problem for determinization:";
              Debug.print @@ lazy (PCSP.Problem.str_of problem);
              Debug.print @@ lazy "");
            match PCSP.ForwardPropagate.solve problem with
            | Ok (PCSP.Problem.Sat subs) ->
                if print_log then
                  Debug.print
                  @@ lazy
                       ("solution:\n"
                       ^ Logic.str_of_term_subst Logic.ExtTerm.str_of subs);
                let ds =
                  Map.Poly.map det ~f:(fun (senv, t) ->
                      (senv, Logic.ExtTerm.subst subs t))
                in
                (* if print_log then (
                   print_endline
                     (sprintf "determinized strategy for %s:"
                        (player_to_string p));
                   Map.Poly.iteri ds ~f:(fun ~key ~data:(senv, t) ->
                       print_endline
                       @@ sprintf "%s: %s" (Ident.name_of_tvar key)
                            (ExTerm.str_of_term params_senv (*ToDo*) senv t))); *)
                `Sat
                  (List.map (Map.Poly.to_alist ds) ~f:(fun (x, (senv, t)) ->
                       let t =
                         fix
                           ~f:(Logic.Term.subst (Map.Poly.map ds ~f:snd))
                           ~equal:Stdlib.( = ) t
                       in
                       ( (x, T_bool.SBool),
                         Some (Logic.ExtTerm.to_old_trm Map.Poly.empty senv t)
                       )))
            | Ok (PCSP.Problem.Unsat _) -> assert false
            | Ok PCSP.Problem.Unknown -> assert false
            | Ok (PCSP.Problem.OutSpace _) -> assert false
            | Ok PCSP.Problem.Timeout -> assert false
            | Error err -> failwith (Error.to_string_hum err)))

  (* the problem clauses (keyed by the digest of the clause as printed, before
     the candidate is substituted: a term may hold a closure, which structural
     equality refuses) whose validation question the axiom form proved after
     the native question was left undecided
     ([axiom_first_when_proved] of [questions.clause_check.seq_axiom_fallback]) *)
  let axiom_proved_clauses : (string, unit) Hashtbl.t = Hashtbl.create (module String)

  let clause_key clause = Md5.to_hex (Md5.digest_string (Logic.ExtTerm.str_of clause))

  (* the problem clauses whose validation question was last left undecided
     ([questions.defer_undecided]) *)
  let undecided_clauses : (string, unit) Hashtbl.t = Hashtbl.create (module String)

  (* how many validation questions were asked in the axiom form first, how
     many of those it proved, and how many deferred clauses were not asked;
     read by the tests *)
  let axiom_first_asked = ref 0

  let axiom_first_proved = ref 0

  let deferred_skipped = ref 0

  (* The validation question of a problem clause, [phi] being it
     with the candidate substituted.  Contract: the answer is the one
     [check_clause_nonparam] gives with its own question order.  [key] is
     [clause_key] of the clause, forced only when the switch is on.  A clause the
     axiom form proved before is asked in that form first: [Valid] there is
     [`Unsat] (no countermodel exists, the axiom form being sound), and any
     other outcome asks [check_clause_nonparam] with the axiom form left out,
     which asks the native question exactly as before and drops the clause
     from the table.  Every other clause is asked as before, and enters the
     table when its [`Unsat] came from the axiom form. *)
  (* the problem clauses (by [clause_key]) the piece route decided
     ([questions.by_pieces]) *)
  let pieces_first_clauses : (string, unit) Hashtbl.t =
    Hashtbl.create (module String)

  (* questions asked by pieces and how many that decided; read by the tests *)
  let by_pieces_counts = (ref 0, ref 0)

  (* Contract: [`Unsat] only when every piece of [phi] was proved (by the
     axiom form or natively), so [phi] is valid; [`Sat m] only with [m] a
     model of a piece's negation, hence of [phi]'s; [`Timeout] otherwise.
     [None] when [phi] has a single piece, which the ordinary route has
     already asked whole. *)
  let check_by_pieces ~axiom_ms ~native_ms fenv phi =
    match ClausePieces.of_clause phi with
    | [] | [ _ ] -> None
    | pieces ->
        incr (fst by_pieces_counts);
        let proved_by_axioms p =
          match
            Z3Smt.Z3interface.with_seq_axiom_fallback
              ~caller_timeout:(Some axiom_ms) ~id fenv p `Timeout
          with
          | `Valid -> true
          | _ -> false
        in
        let native p =
          let saved = !suppress_clause_axiom_fallback in
          suppress_clause_axiom_fallback := true;
          Exn.protect
            ~f:(fun () ->
              check_clause_nonparam_smt ~timeout:(Some native_ms) fenv p)
            ~finally:(fun () -> suppress_clause_axiom_fallback := saved)
        in
        (* An instrument: with [COAR_PIECES_TRACE=dir], each piece asked is
           one line of [dir/pieces.tsv] (the question's number, the piece's
           position and count, the digest of its printed form, its size, the
           route that decided it and the seconds it took) and its printed
           form [dir/piece_<digest>.txt] once per digest.  It changes nothing
           it records. *)
        let trace_dir =
          match Sys.getenv "COAR_PIECES_TRACE" with
          | None | Some "" -> None
          | Some d -> Some d
        in
        let qn = !(fst by_pieces_counts) in
        let total = List.length pieces in
        let trace i p outcome started =
          Option.iter trace_dir ~f:(fun dir ->
              let text = Formula.str_of p in
              let digest = Md5.to_hex (Md5.digest_string text) in
              let file = sprintf "%s/piece_%s.txt" dir digest in
              if not (Sys_unix.file_exists_exn file) then
                Out_channel.write_all file ~data:text;
              Out_channel.with_file (dir ^ "/pieces.tsv") ~append:true
                ~f:(fun oc ->
                  Out_channel.output_string oc
                    (sprintf "%d\t%d\t%d\t%s\t%d\t%s\t%.3f\n" qn i total digest
                       (String.length text) outcome (elapsed_since started))))
        in
        let rec go i undecided = function
          | [] -> if undecided then `Timeout else `Unsat
          | p :: rest -> (
              let started = Common.Clock.now_float () in
              if proved_by_axioms p then (
                trace i p "axioms" started;
                go (i + 1) undecided rest)
              else
                match native p with
                | `Unsat ->
                    trace i p "native-unsat" started;
                    go (i + 1) undecided rest
                | `Sat m ->
                    trace i p "native-sat" started;
                    `Sat m
                | `Timeout ->
                    trace i p "timeout" started;
                    go (i + 1) true rest
                | `Unknown r ->
                    trace i p ("unknown " ^ r) started;
                    go (i + 1) true rest)
        in
        let go = go 0 in
        let res =
          Common.PhaseTime.with_phase "by-pieces" (fun () -> go false pieces)
        in
        (match res with
        | `Unsat | `Sat _ -> incr (snd by_pieces_counts)
        | _ -> ());
        Some res

  (* [key] ([clause_key]: the clause printed whole and digested) is forced
     only when a table it is looked up in is nonempty ([Hashtbl.mem_lazy]):
     on a problem with no sequence sort no axiom-form proof is ever recorded,
     and forcing it for every question of every round only built a string as
     large as the clause.  The same questions are asked in the same order *)
  let check_validation_clause_ordinary ~key ~timeout fenv phi =
    if
      Config.axiom_first_when_proved config.questions.clause_check.seq_axiom_fallback
      && Hashtbl.mem_lazy axiom_proved_clauses key
    then (
      Int.incr axiom_first_asked;
      match
        Common.PhaseTime.with_phase "seq-axiom-first" (fun () ->
            Z3Smt.Z3interface.with_seq_axiom_fallback
              ~caller_timeout:(cap_timeout timeout) ~id fenv phi `Timeout)
      with
      | `Valid ->
          Int.incr axiom_first_proved;
          `Unsat
      | _ ->
          Hashtbl.remove axiom_proved_clauses (Lazy.force key);
          let saved = !suppress_clause_axiom_fallback in
          suppress_clause_axiom_fallback := true;
          Exn.protect
            ~f:(fun () -> check_clause_nonparam ~timeout fenv phi)
            ~finally:(fun () -> suppress_clause_axiom_fallback := saved))
    else
      let asked_before = !clause_check_seq_axiom_asked in
      let res = check_clause_nonparam ~timeout fenv phi in
      (match res with
      | `Unsat
        when Config.axiom_first_when_proved
               config.questions.clause_check.seq_axiom_fallback
             && !clause_check_seq_axiom_asked > asked_before ->
          Hashtbl.set axiom_proved_clauses ~key:(Lazy.force key) ~data:()
      | _ -> ());
      res

  (* [check_validation_clause_ordinary], and with [questions.by_pieces] the
     piece route: after an undecided ordinary answer for a quantified
     question, or first for a clause the piece route decided before (then the
     ordinary route only when the pieces leave it undecided).  Every answer is
     one of the two routes', each sound. *)
  (* [questions.range_pins]: [r] when it is decided, when no width is
     configured, or when [phi] is quantifier-free; otherwise the first
     countermodel of [phi] pinned at a configured width
     ([Ast.RangePin.pinned_question], whose countermodel is one of [phi]),
     and [r] when no width gives one.  Never answers [`Unsat] from a pinned
     question, so it only ever turns an undecided answer into a
     counterexample. *)
  let with_range_pins ~timeout fenv phi r =
    match r with
    | `Sat _ | `Unsat -> r
    | _ when List.is_empty config.questions.range_pins -> r
    | _ when Formula.is_quantifier_free phi -> r
    | _ ->
        let rec go = function
          | [] -> r
          | width :: rest -> (
              match Ast.RangePin.pinned_question ~width phi with
              | None -> r
              | Some q -> (
                  Common.PhaseTime.event "range-pin-asked";
                  match
                    Common.PhaseTime.with_phase "range-pin" (fun () ->
                        check_clause_nonparam ~timeout fenv q)
                  with
                  | `Sat _ as countermodel ->
                      Common.PhaseTime.event "range-pin-countermodel";
                      Debug.print
                      @@ lazy
                           (sprintf
                              "[range pin] width %d gave a countermodel" width);
                      countermodel
                  | _ -> go rest))
        in
        go config.questions.range_pins

  let check_validation_clause_unmemoised ~key ~timeout fenv phi =
    with_range_pins ~timeout fenv phi
    @@
    match (ValidatorConfig.QuestionsSwitch.validation_by_pieces config) with
    | Some (axiom_ms, native_ms) when not (Formula.is_quantifier_free phi) -> (
        let by_pieces () =
          check_by_pieces ~axiom_ms ~native_ms fenv phi
        in
        let decided = function `Unsat | `Sat _ -> true | _ -> false in
        let first =
          if Hashtbl.mem_lazy pieces_first_clauses key then by_pieces ()
          else None
        in
        match first with
        | Some r when decided r -> r
        | Some _ ->
            Hashtbl.remove pieces_first_clauses (Lazy.force key);
            check_validation_clause_ordinary ~key ~timeout fenv phi
        | None -> (
            let r = check_validation_clause_ordinary ~key ~timeout fenv phi in
            if decided r then r
            else
              match by_pieces () with
              | Some r' when decided r' ->
                  Hashtbl.set pieces_first_clauses ~key:(Lazy.force key) ~data:();
                  r'
              | _ -> r))
    | _ -> check_validation_clause_ordinary ~key ~timeout fenv phi

  (* [questions.memo] other than [No_memo]: the decided-valid validation
     questions of this solve, keyed by the question with its bound variables
     renamed in order of occurrence ([alpha_key]), and the undecided ones with
     the budget they were asked under (read only under [Proved_and_undecided]) *)
  let validation_memo : (Formula.t, [ `Valid | `Undecided of int option ]) Hashtbl.t =
    Hashtbl.PolyDeep.create ()

  (* how many validation questions the memo answered; read by the tests *)
  let validation_memo_hits = ref 0

  (* [phi] with every bound variable renamed by a counter in traversal order,
     its free variables kept: two questions differing only in bound names get
     the same key when no reserved spelling blocks it; names already spelled
     anywhere in the question are never captured. Collisions can cause a
     conservative cache miss, never reuse across distinct free variables. *)
  let alpha_key phi =
    let n = ref 0 in
    let taken = Formula.names_spelled_in phi in
    let rec next () =
      incr n;
      let x = Ident.Tvar (sprintf "#vmemo%d" !n) in
      if Set.mem taken x then next () else x
    in
    Formula.aconv_tvar_norm next phi

  (* Contract: as [check_validation_clause_unmemoised], except that unless
     [questions.memo] is [No_memo] a question whose [alpha_key] an earlier
     question proved valid is answered [`Unsat] unasked (and, under
     [Proved_and_undecided], one an earlier question left undecided under the
     same budget is answered [`Timeout] unasked). *)
  let read_instances_dump_count = Atomic.make 0

  let check_validation_clause ~key fenv phi =
    let phi =
      if config.questions.rewrites.unfold_eliminable_apps then
        Evaluator.unfold_eliminable_apps ~fenv phi
      else phi
    in
    (* an equivalence, the identity unless configured *)
    let phi = Ast.RangePin.expand_ground_configured phi in
    (* the budget is the question's as built: a question the rewrite leaves
       quantifier-free keeps the quantified budget it had, rather than the
       quantifier-free one, which is none by default *)
    let timeout = timeout_for phi in
    let phi =
      if config.questions.rewrites.onepoint
         && not (Formula.is_quantifier_free phi)
      then
        Common.PhaseTime.with_phase "onepoint" (fun () ->
            Evaluator.elim_onepoint_singleton_and_split_binders phi)
      else phi
    in
    let phi =
      if config.questions.rewrites.seq_pointwise_extract
         && not (Formula.is_quantifier_free phi)
      then
        Common.PhaseTime.with_phase "pointwise-extract" (fun () ->
            Evaluator.seq_pointwise_eqs_as_extract phi)
      else phi
    in
    (* [questions.read_instances_first_ms]: a weakening of the negation,
       asked first; its [unsat] proves the clause, anything else leaves the
       question to the ordinary route *)
    let check_validation_clause_unmemoised ~key ~timeout fenv phi =
      match config.questions.read_instances_first_ms with
      | Some ms when not (Formula.is_quantifier_free phi) -> (
          match
            try
              Ast.QuestionRewrites.int_universals_at_positions
                (Formula.mk_neg phi)
            with exn_ when not (Common.Timer.is_async exn_) -> None
          with
          | None -> check_validation_clause_unmemoised ~key ~timeout fenv phi
          | Some w ->
              Common.PhaseTime.event "validation-read-instances";
              let proved =
                Common.PhaseTime.with_phase "read-instances" @@ fun () ->
                match
                  ForkedQuery.valid_within ~ms (fun () ->
                      let q = Formula.mk_neg w in
                      (* [COAR_DUMP_READ_INSTANCES=dir] (instrument only): as
                         for the drop-proved step's instance question *)
                      Z3Smt.Z3interface.with_validity_dump ~native:true
                        ~var:"COAR_DUMP_READ_INSTANCES"
                        ~counter:read_instances_dump_count ~id:None ~timeout:ms
                        ~outcome:(function
                          | `Valid -> "valid"
                          | `Invalid _ -> "invalid"
                          | _ -> "undecided")
                        fenv q
                      @@ fun () ->
                      Z3Smt.Z3interface.check_valid ~timeout:(Some ms) ~id:None
                        fenv q)
                with
                | `Valid -> true
                | _ -> false
              in
              if proved then (
                Common.PhaseTime.event "validation-read-instances-proved";
                `Unsat)
              else check_validation_clause_unmemoised ~key ~timeout fenv phi)
      | _ -> check_validation_clause_unmemoised ~key ~timeout fenv phi
    in
    match config.questions.memo with
    | No_memo -> check_validation_clause_unmemoised ~key ~timeout fenv phi
    | (Proved_only | Proved_and_undecided) as memo -> (
      let k = alpha_key phi in
      match Hashtbl.find validation_memo k with
      | Some `Valid ->
          Int.incr validation_memo_hits;
          `Unsat
      | Some (`Undecided t)
        when (match memo with
             | Proved_and_undecided -> true
             | Proved_only | No_memo -> false)
             && Option.equal Int.equal t timeout ->
          Int.incr validation_memo_hits;
          `Timeout
      | _ ->
          let res = check_validation_clause_unmemoised ~key ~timeout fenv phi in
          (match res with
          | `Unsat -> Hashtbl.set validation_memo ~key:k ~data:`Valid
          | `Sat _ -> ()
          | _ -> Hashtbl.set validation_memo ~key:k ~data:(`Undecided timeout));
          res)

  (* With [COAR_DUMP_VALIDATION_QUESTIONS=dir] in the environment, each
     non-parametric clause question of validation is recorded: one line of
     [dir/meta.tsv] (the question's number and process, seconds since the
     first, the digest of its printed form, its size, whether it is
     quantifier-free, reads a sequence and is one the solver may not return
     on, the outcome, the seconds it took and whether it reached the
     sequence-axiom fallback, and the digest of the problem clause it
     comes from), its printed form once per digest as
     [dir/phi_<digest>.txt], the problem clause's once per digest as
     [dir/clause_<digest>.txt], and every solver check it made as SMT-LIB under
     [dir/vN-PID_K.smt2].  A diagnostic: without the variable nothing is
     written and the answer is the same. *)
  (* An instrument, read once: with [COAR_PREPARE_TRACE] set, the
     preparation of the validation questions prints, as it goes, each
     candidate definition's tree and DAG size and, per clause, the sizes
     after substitution, conversion and simplification with the time each
     step ended at.  It changes nothing it measures. *)
  let prepare_trace = Option.is_some (Sys.getenv "COAR_PREPARE_TRACE")

  let validation_dump_count = Atomic.make 0

  let validation_dump_start = lazy (Common.Clock.now_float ())

  let validation_question_dump ~clause phi f =
    match Sys.getenv "COAR_DUMP_VALIDATION_QUESTIONS" with
    | None | Some "" -> f ()
    | Some dir ->
        let t0 = Lazy.force validation_dump_start in
        let n = Atomic.fetch_and_add validation_dump_count 1 in
        let pid = Common.ForkGuard.self_pid () in
        let text = Formula.str_of phi in
        let digest = Md5.to_hex (Md5.digest_string text) in
        let file = sprintf "%s/phi_%s.txt" dir digest in
        if not (Sys_unix.file_exists_exn file) then
          Out_channel.write_all file ~data:text;
        let clause_text = Logic.ExtTerm.str_of clause in
        let clause_digest = Md5.to_hex (Md5.digest_string clause_text) in
        (let file = sprintf "%s/clause_%s.txt" dir clause_digest in
         if not (Sys_unix.file_exists_exn file) then
           Out_channel.write_all file ~data:clause_text);
        let fallback0 = !clause_check_seq_axiom_asked in
        let started = Common.Clock.now_float () in
        let r =
          Z3Smt.Z3interface.with_query_dump (sprintf "%s/v%d-%d" dir n pid) f
        in
        let secs = elapsed_since started in
        Out_channel.with_file (dir ^ "/meta.tsv") ~append:true ~f:(fun oc ->
            Out_channel.output_string oc
              (sprintf "v%d-%d\t%.3f\t%s\t%d\t%b\t%b\t%b\t%s\t%.3f\t%d\t%s\n" n
                 pid
                 (Time_float.Span.to_sec (Time_float.diff started t0))
                 digest (Formula.ast_size phi)
                 (Formula.is_quantifier_free phi)
                 (reads_sequence phi)
                 (Z3Smt.Z3interface.may_not_return
                    (Formula.mk_neg phi))
                 (match r with
                 | `Sat _ -> "sat"
                 | `Unsat -> "unsat"
                 | `Timeout -> "timeout"
                 | `Unknown s -> "unknown:" ^ String.substr_replace_all s ~pattern:"\t" ~with_:" ")
                 secs
                 (!clause_check_seq_axiom_asked - fallback0)
                 clause_digest));
        r

  (* AN ACCOUNT OF THE PHASE'S CLAUSE QUESTIONS BY OUTCOME.  With the
     phase-time report on, each clause question of [find_all_counterexamples]
     is counted under [validation-q/<kind>/<outcome>] with its wall time
     ([kind] is [clause] for a non-parametric question, [param] for a
     parametric one; the outcome is [sat], [unsat], [timeout] or
     [unknown:<reason>]), once more under [.../slow] when it took a second
     or more, and under [.../over7s] when it took 7 s or more, so that a run whose validation time went to exhausted budgets
     says which kind of question did so and with what answer.  It reads a
     clock and adds to a table; with the report off it is one test of a
     flag, and the answer is never changed. *)
  let validation_reason_tag reason =
    String.map reason ~f:(fun c -> if Char.is_alphanum c then c else '-')
    |> fun s -> String.prefix s 40

  let account_validation_question ~kind f =
    if not !Common.PhaseTime.on then f ()
    else
      let t0 = Common.PhaseTime.now () in
      let record o =
        let dt = Common.PhaseTime.now () -. t0 in
        let row = sprintf "validation-q/%s/%s" kind o in
        Common.PhaseTime.add row dt;
        if Float.(dt >= 1.) then Common.PhaseTime.add (row ^ "/slow") dt;
        (* 7 s is 2 s past the 5 s budget of a quantified question: a row
           here is a question whose budget did not hold, which is how an
           overrun inside Z3 shows up beside the timeouts that did hold *)
        if Float.(dt >= 7.) then Common.PhaseTime.add (row ^ "/over7s") dt
      in
      match f () with
      | r ->
          record
            (match r with
            | `Sat _ -> "sat"
            | `Unsat -> "unsat"
            | `Timeout -> "timeout"
            | `Unknown reason -> "unknown:" ^ validation_reason_tag reason);
          r
      | exception e ->
          record "raised";
          raise e

  (* [stop]: once it holds, a clause not yet asked about is not asked, and is
     answered as a question the solver left undecided (the vacuous
     counterexample below), so the candidate is rejected and nothing is
     learnt from that clause *)
  (* [retry_undecided phi res] is given each non-parametric clause's answer
     [res] after it was asked (never one [stop] kept from being asked) and
     returns the answer used; the identity by default *)
  let find_all_counterexamples ?(record = fun _ _ -> ())
      ?(stop = fun () -> false) ?(retry_undecided = fun _ res -> res) clauses
      fenv ((params_senv, cand) : CandSol.t) =
    param_values := Map.Poly.empty;
    let cand_map = CandSol.to_subst (params_senv, cand) in
    let cls_nonparam, cls_param =
      Set.partition_tf ~f:(fst >> Quintuple.trd >> Map.Poly.is_empty)
      @@ Common.PhaseTime.with_phase "prepare"
      @@ fun () ->
      if prepare_trace then
        Map.Poly.iteri cand_map ~f:(fun ~key ~data ->
            Printf.eprintf
              "[prepare-trace] cand %s tree=%d dag=%d selected-tree=%d\n%!"
              (Ident.name_of_tvar key)
              (Logic.Term.ast_size_up_to 100_000_000 data)
              (Qelim.dag_size_up_to 100_000_000 data)
              (Logic.Term.ast_size_up_to 100_000_000
                 (Logic.select_constant_cases data)));
      Set.Poly.map clauses ~f:(fun cl ->
          let tr_t0 = Common.Clock.now_float () in
          let tr_lap name =
            if prepare_trace then
              Printf.eprintf "[prepare-trace]   %s %.3f\n%!" name
                (elapsed_since tr_t0)
          in
          let uni_senv, clause = Clause.to_senv_formula cl in
          if print_log then
            Debug.print
            @@ lazy
                 (sprintf "[check clause] [%d] %s"
                    (Logic.ExtTerm.ast_size clause)
                 @@ Formula.str_of
                 @@ Logic.ExtTerm.to_old_fml
                      (PCSP.Problem.senv_of APCSP.problem)
                      (Map.force_merge params_senv uni_senv)
                      clause);
          if prepare_trace then
            (let apps = ref 0 and arity = ref 0 in
             let rec walk t =
               match t with
               | Logic.App _ -> (
                   let h, args = Logic.Term.let_apps t in
                   (match h with
                   | Logic.Var (x, _) when Map.Poly.mem cand_map x ->
                       incr apps;
                       arity := !arity + List.length args
                   | _ -> walk h);
                   List.iter args ~f:walk)
               | Logic.Bin (_, _, _, b, _) | Logic.TyApp (b, _, _)
               | Logic.TyLam (_, b, _) ->
                   walk b
               | Logic.Let (_, _, a, b, _) ->
                   walk a;
                   walk b
               | Logic.Var _ | Logic.Con _ -> ()
             in
             walk clause;
             Printf.eprintf
               "[prepare-trace] clause tree=%d cand-apps=%d arity-sum=%d\n%!"
               (Logic.Term.ast_size_up_to 100_000_000 clause)
               !apps !arity);
          let phi = Logic.Term.subst cand_map clause in
          if prepare_trace then (
            tr_lap "subst";
            Printf.eprintf "[prepare-trace]   subst tree=%d dag=%d\n%!"
              (Logic.Term.ast_size_up_to 100_000_000 phi)
              (Qelim.dag_size_up_to 100_000_000 phi));
          if print_log then
            Debug.print
            @@ lazy
                 (sprintf "[substituted clause] [%d] %s"
                    (Logic.ExtTerm.ast_size phi)
                    (Formula.str_of
                    @@ Logic.ExtTerm.to_old_fml
                         (PCSP.Problem.senv_of APCSP.problem)
                         (Map.force_merge params_senv uni_senv)
                         phi));
          let phi =
            try
              Logic.ExtTerm.to_old_fml Map.Poly.empty
                (Map.force_merge params_senv uni_senv)
                phi
            with exn_ when not (Common.Timer.is_async exn_) ->
              failwith
                (sprintf "failed to convert term %s to old formula: %s"
                   (Logic.ExtTerm.str_of phi)
                   (CandSol.str_of (params_senv, cand)))
          in
          if prepare_trace then (
            tr_lap "to-old";
            Printf.eprintf "[prepare-trace]   old size=%d\n%!"
              (Formula.ast_size phi));
          let phi = Evaluator.simplify phi in
          if prepare_trace then (
            tr_lap "simplify";
            Printf.eprintf "[prepare-trace]   simplified size=%d\n%!"
              (Formula.ast_size phi));
          if print_log then
            Debug.print
            @@ lazy (sprintf "[simplified clause] %s" (Formula.str_of phi));
          let fvs = Formula.tvs_of phi in
          let uni_senv' = Map.Poly.filter_keys uni_senv ~f:(Set.mem fvs) in
          let params_senv' =
            Map.Poly.filter_keys params_senv ~f:(Set.mem fvs)
          in
          ( (uni_senv, clause, params_senv', uni_senv', phi),
            (ClauseGraph.Clause cl, true) ))
    in
    (* [questions.defer_undecided]: the clauses an earlier round left
       undecided go last, and are skipped once a clause before them gave a
       counterexample *)
    let cls_first, cls_deferred =
      let l = Set.to_list cls_nonparam in
      if config.questions.defer_undecided then
        List.partition_tf l ~f:(fun ((_, clause, _, _, _), _) ->
            not (Hashtbl.mem_lazy undecided_clauses (lazy (clause_key clause))))
      else (l, [])
    in
    let found_counterexample = ref false in
    let ask_nonparam ~deferred ((uni_senv, clause, _, _, phi), cl) =
      (* non-parametric candidate solution *)
      let skipped = deferred && !found_counterexample in
      let key = lazy (clause_key clause) in
      if skipped then Int.incr deferred_skipped;
      let asked = not (stop () || skipped) in
      let result =
        if not asked then `Timeout
        else
          account_validation_question ~kind:"clause"
          @@ fun () ->
          retry_undecided phi
          @@ Common.PhaseTime.with_phase "check"
          @@ fun () ->
          validation_question_dump ~clause phi @@ fun () ->
          check_validation_clause ~key fenv phi
      in
      (match result with
      | `Sat _ -> found_counterexample := true
      | `Unsat -> ()
      | _ ->
          (* a clause the solver was asked about and decided neither way:
             reported to the dynamic encoding, which acts only on clauses it
             armed (see [PCSatCommon.RecFunDynamic]) *)
          if asked then
            match cl with
            | ClauseGraph.Clause c, _ -> PCSatCommon.RecFunDynamic.note_undecided c
            | _ -> ());
      if config.questions.defer_undecided && not skipped then (
        match result with
        | `Sat _ | `Unsat -> Hashtbl.remove undecided_clauses (Lazy.force key)
        | _ -> Hashtbl.set undecided_clauses ~key:(Lazy.force key) ~data:());
      (([ (uni_senv, clause) ], phi, result), Set.Poly.singleton cl)
    in
    let cls_nonparam =
      let first = List.map cls_first ~f:(ask_nonparam ~deferred:false) in
      let deferred = List.map cls_deferred ~f:(ask_nonparam ~deferred:true) in
      Set.Poly.of_list (first @ deferred)
    in
    (* The parametric clauses are asked in groups, one question
       [exists params. forall x. /\ group] per group, so two groups must share
       no parameter: each question picks its own values for the parameters it
       mentions.  A group is therefore a connected component of the relation
       "shares a parameter", closed transitively.  Relating each clause only to
       a group's first member ([List.classify]) split a chain: with
       [P := p1 <= p2] and [Q := p3 <= p4], [P(0)], [P x => Q x] and
       [Q x => x >= 1] went into {[P(0)], [P x => Q x]} and {[Q x => x >= 1]},
       each satisfiable alone (by [p3 <= p4] and by [p3 > p4]), and a problem
       with no solution was answered [sat]. *)
    let param_components rs =
      let key ((_, _, senv, _, _), _) = Map.Poly.key_set senv in
      let rec grow members keys rest =
        let joined, rest =
          List.partition_tf rest ~f:(fun r ->
              Fn.non Set.is_empty @@ Set.inter keys (key r))
        in
        if List.is_empty joined then (members, rest)
        else
          grow (members @ joined)
            (Set.Poly.union_list (keys :: List.map joined ~f:key))
            rest
      in
      let rec go = function
        | [] -> []
        | r :: rest ->
            let members, rest = grow [ r ] (key r) rest in
            members :: go rest
      in
      go rs
    in
    let cls_param =
      Set.to_list cls_param |> param_components
      |> List.map ~f:(fun rs ->
          let (cls, params_senv', uni_senv', phi), cl =
            List.fold rs
              ~init:
                ( ([], Map.Poly.empty, Map.Poly.empty, Formula.mk_true ()),
                  Set.Poly.empty )
              ~f:(fun
                  ((cls, params_senv, uni_senv, phi), srcs)
                  ((uni_senv0, clause0, params_senv', uni_senv', phi'), src_cl)
                ->
                ( ( (uni_senv0, clause0) :: cls,
                    Map.force_merge params_senv params_senv',
                    Map.force_merge uni_senv uni_senv',
                    Formula.mk_and phi phi' ),
                  Set.add srcs src_cl ))
          in
          (* parametric candidate solution *)
          assert config.parametric_candidates;
          ( ( cls,
              phi,
              if stop () then `Timeout
              else if config.strategy_synthesis then (
                (* apply strategy synthesis to forall-exists formula *)
                assert config.parametric_examples;
                check_clause_param_strat_synth ~timeout:(timeout_for phi) fenv
                  params_senv' uni_senv' phi)
              else
                (* apply SMT solving to forall-exists formula *)
                account_validation_question ~kind:"param" (fun () ->
                    check_clause_param_smt ~timeout:(timeout_for phi) fenv
                      params_senv' uni_senv' phi) ),
            cl ))
      |> Set.Poly.of_list
    in
    Set.union cls_nonparam cls_param
    |> Set.concat_map ~f:(fun ((cls, phi, res), src_cl) ->
        match res with
        | `Sat model ->
            (* not all but some clause in cls has a countermodel *)
            let res =
              Set.Poly.union_list
              @@ List.map cls ~f:(fun (uni_senv, clause) ->
                  let phi_clause =
                    Logic.ExtTerm.to_old_fml
                      (PCSP.Problem.senv_of APCSP.problem)
                      uni_senv clause
                  in
                  let sub, exs =
                    ExClauseSet.of_model_with_subst ~discharge:(discharge fenv)
                      ~stated_literals:
                        (if config.examples.generalise_invented_values then
                           Some (Lazy.force stated_literals)
                         else None)
                      ~partial_model:config.examples.partial_model.examples
                      ~partial_seq_elements:
                        (Config.ExamplesSwitch.partial_seq_elements config)
                      ~partial_seq_elements_goal_only:
                        (Config.ExamplesSwitch.partial_seq_elements_goal_only config)
                      ~group_equal:config.examples.partial_model.group_equal_values
                      ~settle_pure:config.examples.partial_model.settle_pure
                      ~open_vars:
                        (if config.examples.fn_results_open then (
                           let fns = PCSP.Problem.fnpvs_of APCSP.problem in
                           let open_vars =
                             ExClauseSet.fn_result_vars
                               ~is_fn:(fun pv ->
                                 Set.mem fns (Ident.pvar_to_tvar pv))
                               (PCSP.Problem.senv_of APCSP.problem)
                               phi_clause
                           in
                           (* act counter: an example left with an open
                              result variable *)
                           if not (Set.is_empty open_vars) then
                             Common.PhaseTime.event "examples/fn-results-open";
                           open_vars)
                         else Set.Poly.empty)
                      (PCSP.Problem.senv_of APCSP.problem)
                      config.parametric_examples (uni_senv, phi_clause) model
                  in
                  let exs =
                    Set.Poly.map exs
                      ~f:
                        (ExClause.simplify_wfpvs
                           (PCSP.Problem.wfpvs_of APCSP.problem))
                  in
                  (* the counterexample's region, beside its point, for a clause
                     demanding a well-founded unknown; only for a group of one
                     clause, whose candidate-substituted formula is [phi] *)
                  let exs =
                    if
                      (Config.ExamplesSwitch.wf_region_examples config) && config.parametric_examples
                      && List.length cls = 1
                    then
                      match
                        PCSatCommon.WfRegion.example ~id
                          ~timeout_ms:(Config.ExamplesSwitch.wf_region_examples_timeout_ms config)
                          ~discharge:(discharge fenv) ~fenv
                          ~exi_senv:(PCSP.Problem.senv_of APCSP.problem)
                          ~wfpvs:(PCSP.Problem.wfpvs_of APCSP.problem)
                          ~clause:phi_clause ~refuted:phi model
                      with
                      | Ok ex ->
                          let ex =
                            ExClause.simplify_wfpvs
                              (PCSP.Problem.wfpvs_of APCSP.problem)
                              ex
                          in
                          Debug.print
                          @@ lazy ("[wf region] " ^ ExClause.str_of ex);
                          (* beside the point, which is recorded as one a
                             region reader must skip (see
                             [WfRegion.note_generalised_point]) *)
                          Set.iter exs
                            ~f:PCSatCommon.WfRegion.note_generalised_point;
                          Set.add exs ex
                      | Error _ -> exs
                    else exs
                  in
                  (* the counterexample's region projected onto the atoms'
                     arguments, beside its point (never in place of it); only
                     for a group of one clause, whose candidate-substituted
                     formula is [phi] *)
                  let exs =
                    match Config.ExamplesSwitch.projected_region_timeout_ms config with
                    | Some timeout_ms
                      when config.parametric_examples && List.length cls = 1 -> (
                        match
                          PCSatCommon.ProjectedRegion.example ~id ~timeout_ms
                            ~discharge:(discharge fenv) ~fenv
                            ~exi_senv:(PCSP.Problem.senv_of APCSP.problem)
                            ~clause:phi_clause ~refuted:phi model
                        with
                        | Ok ex ->
                            let ex =
                              ExClause.simplify_wfpvs
                                (PCSP.Problem.wfpvs_of APCSP.problem)
                                ex
                            in
                            Debug.print
                            @@ lazy ("[projected region] " ^ ExClause.str_of ex);
                            Set.add exs ex
                        | Error _ -> exs)
                    | _ -> exs
                  in
                  (* the goal clause's own read indices, beside the example
                     and keyed by its atoms; only a goal clause is recorded
                     here, so that every record is the whole of what the
                     clause's refutation reads *)
                  (if config.examples.record.goal_reads then
                     let n =
                       GoalReads.record_instance ~allow_step:false phi_clause sub
                     in
                     if n > 0 then
                       Debug.print
                       @@ lazy
                            (sprintf "[goal reads] recorded for %d body atom(s) (%d keys)"
                               n (GoalReads.size ())));
                  (* the head's refuting index, beside each positive example
                     the counterexample produced *)
                  (if config.examples.record.head_witnesses then
                     let ws = head_witness_values model in
                     let n =
                       GoalReads.record_head_witnesses
                         (List.concat_map (Set.to_list exs) ~f:(fun ex ->
                              Set.to_list ex.ExClause.positive))
                         ws
                     in
                     if n > 0 then
                       Debug.print
                       @@ lazy
                            (sprintf "[head witnesses] %s recorded for %d head atom(s)"
                               (String.concat_map_list ~sep:"," ws ~f:Z.to_string)
                               n));
                  let exs =
                    if config.examples.record.premise_instances then
                      match premise_instances_of sub phi_clause with
                      | None -> exs
                      | Some phi ->
                          (* every free variable left in the fact is a parameter
                             the model did not pin down; an [FCon] is unbound
                             without their sorts *)
                          let params =
                            Map.of_set_exn @@ Formula.term_sort_env_of phi
                          in
                          Set.Poly.map exs
                            ~f:(ExClause.add_cond_with_params params phi)
                    else exs
                  in
                  let exs, sub =
                    if not config.examples.fact_clause_examples then (exs, sub)
                    else
                      match fact_example_of clause with
                      | Some ex ->
                          (* BESIDE the model's point, not instead of it: the
                             synthesis phase grounds a parametric example at
                             a few instances, so a candidate can satisfy what
                             it is given of the clause and still violate the
                             clause, and then the clause comes back as the same
                             example and the round learns nothing -- measured,
                             a lost answer on an input that answered in six
                             seconds.  The point is new each round. *)
                          (Set.add exs ex, sub)
                      | None -> (exs, sub)
                  in
                  (* the fact's maximally partial form, beside the point and
                     recorded under its own (smaller) substitution *)
                  let beside =
                    if
                      config.examples.partial_model.fact_examples
                      && config.parametric_examples
                      && (not config.examples.partial_model.examples)
                      && Option.is_some (fact_example_of clause)
                    then
                      match
                        ExClauseSet.partial_model_beside
                          ~discharge:(discharge fenv)
                          (PCSP.Problem.senv_of APCSP.problem)
                          phi_clause sub
                      with
                      | None -> []
                      | Some (smaller, bs) ->
                          Set.to_list bs
                          |> List.map ~f:(fun ex ->
                              ( ExClause.simplify_wfpvs
                                  (PCSP.Problem.wfpvs_of APCSP.problem)
                                  ex,
                                smaller ))
                          |> List.filter ~f:(fun (ex, _) -> not (Set.mem exs ex))
                    else []
                  in
                  List.iter beside ~f:(fun (ex, _) ->
                      Debug.print
                      @@ lazy
                           ("[partial fact] kept beside the point: "
                          ^ ExClause.str_of ex));
                  (* what this phase PRODUCES, which is what every generalisation
                     mechanism here acts on.  Counted at the producer because a
                     claim about a producer is easy to make and easy to believe:
                     a mechanism can empty the examples of invented values, say
                     so in its own numbers, and buy nothing, which is why the
                     phases downstream count what they receive and what they
                     spend it on. *)
                  PCSatCommon.GeneralityMonitor.(
                    if on () then begin
                      let g, p, c =
                        Set.fold (ExClauseSet.exatoms_of exs) ~init:(0, 0, 0)
                          ~f:(fun (g, p, c) atm ->
                            let _, cond, _ = ExAtom.to_old_formula_and_cond atm in
                            let guarded =
                              if LogicOld.Formula.is_true cond then 0 else 1
                            in
                            if ExAtom.is_ppapp atm then (g, p + 1, c + guarded)
                            else (g + 1, p, c + guarded))
                      in
                      arrive Validation ~ground:g ~parametric:p ~guarded:c
                    end);
                  Set.iter exs ~f:(fun ex -> record ex sub);
                  List.iter beside ~f:(fun (ex, smaller) -> record ex smaller);
                  Set.union exs (Set.Poly.of_list (List.map beside ~f:fst)))
            in
            if Fn.non Set.is_empty res then
              Set.Poly.map res ~f:(fun ex -> (ex, src_cl))
            else
              (* note that res never represents true *)
              let ctx = Z3.mk_context [ ("MODEL", "true") ] in
              let dtenv =
                Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx
                  (PCSP.Problem.dtenv_of APCSP.problem)
              in
              Debug.print
              @@ lazy
                   (sprintf "model: %s\ncandidate: %s\nphi: %s\nz3 input: %s"
                      (str_of_model model)
                      (CandSol.str_of (params_senv, cand))
                      (Formula.str_of phi)
                      (Z3.Expr.to_string
                      @@ Z3Smt.Z3interface.of_formula ~id ctx [] [] fenv dtenv
                      @@ Formula.mk_neg phi));
              (* ToDo: should be unreachable *)
              (*dummy*)
              Set.Poly.singleton
                ( ExClause.mk_unit_pos @@ ExAtom.mk_true (),
                  Set.Poly.singleton (ClauseGraph.Dummy, true) )
        | `Unsat -> Set.Poly.empty
        | _ ->
            (* Z3 did not decide whether the candidate violates this clause.
               What is returned here is a VACUOUS counterexample, and it does
               two incompatible things: it is non-empty, so the caller rejects
               the candidate, and it says nothing, so the example set does not
               grow -- which means the next synthesis proposes the same
               candidate and the loop cannot end.  A ten-line satisfiable
               problem whose validation query Z3 cannot decide over the sequence
               theory runs like that indefinitely, proposing the correct
               invariant on every iteration.  Saying so is the first half of
               being able to bound it. *)
            Debug.print
            @@ lazy
                 "[validation undecided] the solver neither confirmed \
                  nor                   refuted this clause; the candidate is \
                  rejected and nothing is                   learnt from it";
            Common.PhaseTime.event "validation-undecided-clause";
            (let exi = PCSP.Problem.senv_of APCSP.problem in
             List.iter cls ~f:(fun (_, clause) ->
                 round_undecided_unknowns :=
                   Set.union !round_undecided_unknowns
                     (Set.filter (Logic.ExtTerm.fvs_of clause)
                        ~f:(Map.Poly.mem exi))));
            Set.Poly.singleton
              ( ExClause.mk_unit_pos @@ ExAtom.mk_true (),
                Set.Poly.singleton (ClauseGraph.Dummy, true) ))

  (** ToDo: fix to use real MaxSMT *)
  let find_common_counterexamples_for_clause ?(record = fun _ _ -> ()) fenv
      num_ex (candidates : (CandSol.t * CandSol.tag) list) clause =
    let exi_senv = PCSP.Problem.senv_of APCSP.problem in
    let uni_senv, clause = Clause.to_senv_formula clause in
    let cand_phi_list =
      List.map candidates ~f:(fun (cand, cand_tag) ->
          let cand_map = CandSol.to_subst cand in
          ( cand,
            ( cand_tag,
              Formula.mk_neg
              @@ Logic.ExtTerm.to_old_fml uni_senv Map.Poly.empty
                   (Logic.Term.subst cand_map clause) ) ))
    in
    let classified =
      List.map cand_phi_list ~f:(fun ((_, (_, phi)) as e) ->
          (e, Z3Smt.Z3interface.check_sat ~id ~timeout:(timeout_for phi) fenv [ phi ]))
    in
    (* a candidate is genuine for this clause only if Z3 proved it so; an
       unknown/timeout keeps it spurious, as AllExamples does *)
    let spurious_cand_phi_list =
      List.filter_map classified ~f:(function
        | _, `Unsat -> None
        | e, _ -> Some e)
    in
    let undecided =
      List.exists classified ~f:(function
        | _, (`Sat _ | `Unsat) -> false
        | _ -> true)
    in
    let examples =
      List.filter_map classified ~f:(function
        | (_, (CandSol.Total true, phi)), `Sat _ -> Some phi
        | _ -> None)
      |> Z3Smt.Z3interface.max_smt_of ~id fenv num_ex
      |> Set.concat_map ~f:(fun model ->
          let sub, examples =
            ExClauseSet.of_model_with_subst ~discharge:(discharge fenv) exi_senv
              false
              ( Map.force_merge exi_senv uni_senv,
                Logic.ExtTerm.to_old_fml exi_senv uni_senv clause )
              model
          in
          Set.iter examples ~f:(fun ex -> record ex sub);
          (* a countermodel may omit variables Z3 found irrelevant; as in
             [find_all_counterexamples], keep the loop going with a dummy *)
          if Set.is_empty examples then
            Set.Poly.singleton (ExClause.mk_unit_pos @@ ExAtom.mk_true ())
          else examples)
    in
    ( (if undecided then
         (*dummy*)
         Set.add examples (ExClause.mk_unit_pos @@ ExAtom.mk_true ())
       else examples),
      Set.Poly.of_list @@ List.map ~f:fst spurious_cand_phi_list )

  (* [seed_atom_role p ts]: how the refutation cone treats a ground
     application of [p] to [ts], by [p]'s kind: an ordinary unknown's atom
     may take either value; a well-founded unknown's is an edge from the first
     half of its arguments to the second; a parity unknown's an edge from
     (shared arguments, left arguments, left tag) to (shared arguments, right
     arguments, right tag) in its family's graph, the nodes the labeler's
     cycle test uses; every other kind is never removed.  An arity that does
     not split as the kind says is [Fixed]. *)
  let seed_atom_role p ts =
    let str ts = String.concat ~sep:"," (List.map ts ~f:Term.str_of) in
    match PCSP.Problem.kind_of APCSP.problem (Ident.pvar_to_tvar p) with
    | Kind.Ord -> SeededUnfolding.Free
    | Kind.WF when List.length ts % 2 = 0 ->
        let l, r = List.split_n ts (List.length ts / 2) in
        SeededUnfolding.Edge (Ident.name_of_pvar p, str l, str r)
    | Kind.Parity (nwf, (idl, idr)) -> (
        let size_shared = List.length nwf.Kind.sorts_shared in
        match
          ( Hashtbl.Poly.find nwf.Kind.sorts_map idl,
            Hashtbl.Poly.find nwf.Kind.sorts_map idr )
        with
        | Some sl, Some sr
          when List.length ts
               = size_shared + List.length sl + List.length sr ->
            let params, rest = List.split_n ts size_shared in
            let t1, t2 = List.split_n rest (List.length sl) in
            SeededUnfolding.Edge
              ( Ident.name_of_tvar nwf.Kind.name,
                str (params @ t1) ^ "@" ^ Ident.name_of_tvar idl,
                str (params @ t2) ^ "@" ^ Ident.name_of_tvar idr )
        | _ -> SeededUnfolding.Fixed)
    | _ -> SeededUnfolding.Fixed

  (* [seed_examples vs g]: the ground instances of this problem's own clauses
     that a seeded unfolding from its fact clauses reaches under the seeds [g]
     (see [PCSatCommon.SeededUnfolding]), each with the clause it is an
     instance of as its source, as a validator counterexample has; with
     [g.trace], one stderr line saying what was built.  Every member is an
     instance of a clause of the problem, so holding them as examples is
     sound whatever the seeds are: they only choose which instances.  With
     [g.stop_after_fruitless = Some k], once [k] messages in a row of this
     problem kept no instance, a message is not unfolded at all and gives
     no example (the trace line says so); a message that keeps one resets
     the count.  Holding fewer instances is sound for the same reason. *)
  let fruitless_seed_messages = ref 0

  let seed_examples vs (g : PCSP.Problem.ground_seeds) =
    match g.stop_after_fruitless with
    | Some k when !fruitless_seed_messages >= k ->
        let line =
          sprintf
            "ground-seeds: received %d seed(s), not unfolded: %d consecutive \
             messages kept no instance"
            (List.length g.seeds) !fruitless_seed_messages
        in
        Debug.print @@ lazy line;
        if g.trace then (
          Out_channel.output_string stderr (line ^ "\n");
          Out_channel.flush stderr);
        Set.Poly.empty
    | _ ->
        let t0 = Common.PhaseTime.now () in
        let results, stats =
          Common.PhaseTime.with_phase "seeded-unfolding" @@ fun () ->
          PCSatCommon.SeededUnfolding.run
            ~kept_args:(fun q ->
              Option.map ~f:fst
                (Map.Poly.find (PCSP.Problem.args_record_of APCSP.problem) q))
            ~exi_senv:(PCSP.Problem.senv_of APCSP.problem)
            ~atom_budget:g.atom_budget ~max_combos:g.max_combos
            { seeds = g.seeds; atoms = g.atoms; choice_values = g.choice_values }
            (PCSP.Problem.clauses_of APCSP.problem)
        in
        (* an unfolding stopped by its atom or instance budget is declined whole:
           its instances are sound but are thousands of examples that closed no
           lasso within the budget, which only slows every later round *)
        let results = if stats.exhausted then [] else results in
        (* with [g.refutation_cone], only the instances a labeling refutation of
           this message's instances can use (see
           [SeededUnfolding.refutation_cone]): the kept set is refuted exactly
           when the whole set is, so the refutations the seeds were sent for
           stay, and the chains that close no cycle are not held *)
        let results, dropped =
          if g.refutation_cone then
            Common.PhaseTime.with_phase "seeded-cone" (fun () ->
                SeededUnfolding.refutation_cone ~role_of:seed_atom_role results)
          else (results, 0)
        in
        if List.is_empty results then incr fruitless_seed_messages
        else fruitless_seed_messages := 0;
        let exs =
          Set.Poly.of_list
          @@ List.map results ~f:(fun (ex, sub, cl) ->
              VersionSpace.record_derivation vs ex ~rule:"seeded-instance"
                ~subst:(Some sub);
              (ex, Set.Poly.singleton (ClauseGraph.Clause cl, true)))
        in
        let line =
          sprintf "ground-seeds: received %d seed(s) [%s] %s%s%s time=%.3f"
            (List.length g.seeds)
            (String.concat ~sep:","
               (List.map g.seeds ~f:(fun (x, vs) ->
                    x ^ "="
                    ^ String.concat ~sep:"|" (List.map vs ~f:Value.str_of))))
            (PCSatCommon.SeededUnfolding.str_of_stats stats)
            (if stats.exhausted then " declined" else "")
            (if g.refutation_cone then
               sprintf " cone-kept=%d cone-dropped=%d" (List.length results)
                 dropped
             else "")
            (Common.PhaseTime.now () -. t0)
        in
        Debug.print @@ lazy line;
        if g.trace then (
          Out_channel.output_string stderr (line ^ "\n");
          Out_channel.flush stderr);
        exs

  (* [receive_bounds vs]: the bounds the exchange sent are added as learned
     clauses, and the ground seeds it sent (only a configuration that asks
     for them sends any) are turned into examples, returned for this round's
     result with whether a trace was asked and whether synthesis may read
     them (false if any message of the round said so): [None] when no seed
     message was received *)
  let receive_bounds vs =
    match PCSP.Problem.messenger_of APCSP.problem with
    | None -> None
    | Some messenger ->
        let add =
          VersionSpace.add_bound_as_learned_clause ~print:Debug.print id
            APCSP.problem vs
        in
        Common.Messenger.receive_all_infos_with messenger id ~filter:(function
          | PCSP.Problem.(LowerBounds _ | UpperBounds _ | GroundSeeds _) -> true
          | _ -> false)
        |> List.fold ~init:None ~f:(fun seeded -> function
          | _, PCSP.Problem.LowerBounds bounds ->
              Map.Poly.iteri bounds ~f:(fun ~key ~data -> add key data false);
              seeded
          | _, PCSP.Problem.UpperBounds bounds ->
              Map.Poly.iteri bounds ~f:(fun ~key ~data -> add key data true);
              seeded
          | _, PCSP.Problem.GroundSeeds g -> (
              let exs = seed_examples vs g in
              match seeded with
              | None -> Some (exs, g.trace, g.synthesis_reads)
              | Some (exs0, t, r) ->
                  Some
                    (Set.union exs0 exs, t || g.trace, r && g.synthesis_reads))
          | _ -> failwith "receive_bounds")

  let send_candidate_partial_solution vs cexs cand cand_tag cls =
    match PCSP.Problem.messenger_of APCSP.problem with
    | None -> ()
    | Some messenger -> (
        let lbs_opt =
          if config.check_part_sol_with_lbs then
            Some
              ( PCSP.Problem.senv_of APCSP.problem,
                vs.VersionSpace.fenv,
                vs.VersionSpace.lower_bounds )
          else None
        in
        let stable_clauses = PCSP.Problem.stable_clauses_of APCSP.problem in
        (*if Set.is_empty stable_clauses then ()(*ToDo*)
          else*)
        let violated_non_query_clauses =
          Set.concat_map cexs ~f:(fun (_, sources) ->
              (* filter out query clauses *)
              Set.Poly.filter_map sources ~f:(function
                | ClauseGraph.Clause c, _ when not @@ Set.mem stable_clauses c
                  ->
                    Some c
                | _ -> None))
        in
        if Set.is_empty violated_non_query_clauses then
          (*let _ = assert (Set.is_singleton cexs && Stdlib.(=) (snd @@ Set.choose_exn cexs)[ClauseGraph.Dummy, true]) in*)
          (* reachable here if an SMT solving failed *) ()
        else
          let full_non_query_clauses = Set.diff cls stable_clauses in
          Debug.print
          @@ lazy
               (sprintf "full_non_query_clauses:\n%s\n"
               @@ String.concat_map_set ~sep:"\n" full_non_query_clauses
                    ~f:(Clause.str_of (PCSP.Problem.senv_of APCSP.problem)));
          Debug.print
          @@ lazy
               (sprintf "violated_non_query_clauses:\n%s\n"
               @@ String.concat_map_set ~sep:"\n" violated_non_query_clauses
                    ~f:(Clause.str_of (PCSP.Problem.senv_of APCSP.problem)));
          let sol = PCSP.Problem.sol_of_candidate APCSP.problem cand in
          let sol_before_red = CandSol.to_subst cand in
          match cand_tag with
          | CandSol.Partial target_pvar ->
              let partial_sol_cand_of =
                let pvars =
                  Set.Poly.map ~f:(fun ri -> ri.PCSP.Params.name)
                  @@ Map.Poly.find_exn
                       (PCSP.Problem.partial_sol_targets_of APCSP.problem)
                       target_pvar
                in
                fun sol -> Map.Poly.filter_keys sol ~f:(Set.mem pvars)
              in
              Debug.print
              @@ lazy
                   (sprintf
                      "send a candidate partial solution to the messenger for \
                       [%s]"
                   @@ Ident.name_of_tvar target_pvar);
              Common.Messenger.send_boardcast messenger id
              @@ PCSP.Problem.CandidateSolution
                   ( partial_sol_cand_of sol,
                     partial_sol_cand_of sol_before_red,
                     violated_non_query_clauses,
                     full_non_query_clauses,
                     lbs_opt )
          | Total _with_sampling ->
              let target_pvars =
                Map.key_set @@ PCSP.Problem.partial_sol_targets_of APCSP.problem
              in
              if Set.is_empty target_pvars then (
                (*ToDo: this case is necessary because [partial_sol_targets_of pfwcsp] is empty if MuVal's [extra_partial_sols] is [No_extra]*)
                Debug.print
                @@ lazy "send a candidate partial solution to the messenger";
                Common.Messenger.send_boardcast messenger id
                @@ PCSP.Problem.CandidateSolution
                     ( sol,
                       sol_before_red,
                       violated_non_query_clauses,
                       full_non_query_clauses,
                       lbs_opt ))
              else if
                config.check_part_sol_with_lbs
                ||
                (* if [check_part_sol_with_lbs] is false, necessary to satisfy [is_qualified_partial_solution] for some target pvar *)
                Set.exists target_pvars ~f:(fun pvar ->
                    PCSP.Problem.is_qualified_partial_solution
                      ~print:Debug.print
                      (Map.Poly.find_exn
                         (PCSP.Problem.dep_graph_of APCSP.problem)
                         pvar)
                      target_pvars violated_non_query_clauses)
              then (
                Debug.print
                @@ lazy "send a candidate partial solution to the messenger";
                Common.Messenger.send_boardcast messenger id
                @@ PCSP.Problem.CandidateSolution
                     ( sol,
                       sol_before_red,
                       violated_non_query_clauses,
                       full_non_query_clauses,
                       lbs_opt )))

  (* The Houdini-style pre-pass: its fixed point, final check and schedule,
     over this validator's clause checks and the state they share
     ([houdini_window]).  Included, so every name it defines stays a name of
     this module. *)
  include
    Houdini.FixedPoint.Make (Cfg) (APCSP)
      (struct
        let window = houdini_window
        let id = id

        module Debug = Debug

        let check_clause_nonparam = check_clause_nonparam
        let find_all_counterexamples = find_all_counterexamples
        let timeout_for = timeout_for
        let negation_asked = negation_asked
        let cap_ms = cap_ms
        let elapsed_since = elapsed_since
        let binds_sequence_existentially = binds_sequence_existentially
      end)

  (* With [COAR_DUMP_CANDIDATES=dir] in the environment, each total
     candidate validation rejects or accepts is recorded: one line of
     [dir/rounds.tsv] (the round, seconds since the first, the number of
     examples the version space held before the round, the counterexamples
     that carry an example and the vacuous ones an undecided clause gives,
     then one [name:digest] per unknown, the digest taken of the unknown's
     printed definition with every generated name renamed by first
     occurrence, so that a candidate proposed again under fresh bound names
     has the same digest), and each definition once per digest as
     [dir/cand_<digest>.txt].  A diagnostic: without the variable nothing is
     written and nothing else changes. *)
  let candidate_dump_round = ref 0

  let candidate_dump_start = lazy (Common.Clock.now_float ())

  (* every [#letters digits] name of [text] renamed [#gN] by first occurrence *)
  let normalise_generated_names text =
    let tbl = Hashtbl.create (module String) in
    let n = String.length text in
    let buf = Buffer.create n in
    let is_letter c = Char.is_lowercase c || Char.equal c '_' in
    let rec go i =
      if i >= n then ()
      else if Char.equal text.[i] '#' then (
        let j = ref (i + 1) in
        while !j < n && is_letter text.[!j] do incr j done;
        let k = ref !j in
        while !k < n && Char.is_digit text.[!k] do incr k done;
        if !j > i + 1 && !k > !j then (
          let m = String.sub text ~pos:i ~len:(!k - i) in
          let r =
            match Hashtbl.find tbl m with
            | Some r -> r
            | None ->
                let r = sprintf "#g%d" (Hashtbl.length tbl) in
                Hashtbl.set tbl ~key:m ~data:r;
                r
          in
          Buffer.add_string buf r;
          go !k)
        else (
          Buffer.add_char buf '#';
          go (i + 1)))
      else (
        Buffer.add_char buf text.[i];
        go (i + 1))
    in
    go 0;
    Buffer.contents buf

  let candidate_dump vs ((params_senv, cand) : CandSol.t) cexs =
    match Sys.getenv "COAR_DUMP_CANDIDATES" with
    | None | Some "" -> ()
    | Some dir ->
        let t0 = Lazy.force candidate_dump_start in
        let round = !candidate_dump_round in
        incr candidate_dump_round;
        let vacuous (ex, _) =
          Set.is_empty ex.ExClause.negative
          && Set.for_all ex.ExClause.positive ~f:(function
            | ExAtom.FCon (params, phi) ->
                Map.Poly.is_empty params && Formula.is_true phi
            | _ -> false)
        in
        let nvac = Set.count cexs ~f:vacuous in
        let nreal = Set.length cexs - nvac in
        let nex = Set.length (VersionSpace.examples_of vs) in
        let defs =
          Set.to_list cand
          |> List.map ~f:(fun (((Ident.Tvar name, _), _) as b) ->
              let text =
                normalise_generated_names
                  (CandSol.str_of (params_senv, Set.Poly.singleton b))
              in
              let digest = Md5.to_hex (Md5.digest_string text) in
              let file = sprintf "%s/cand_%s.txt" dir digest in
              if not (Sys_unix.file_exists_exn file) then
                Out_channel.write_all file ~data:text;
              sprintf "%s:%s" name (String.prefix digest 8))
        in
        Out_channel.with_file (dir ^ "/rounds.tsv") ~append:true ~f:(fun oc ->
            Out_channel.output_string oc
              (sprintf "%d\t%.3f\t%d\t%d\t%d\t%s\n" round
                 (Time_float.Span.to_sec
                    (Time_float.diff (Common.Clock.now_float ()) t0))
                 nex nreal nvac
                 (String.concat ~sep:" " defs)))

  let validate vs (candidates : (CandSol.t * CandSol.tag) list) =
    Debug.print @@ lazy "**** Validator";
    Debug.print
    @@ lazy
         (String.concat_mapi_list ~sep:"\n" candidates
            ~f:(fun i (candidate, cand_tag) ->
              sprintf "**** %s candidate solution[%s] %s\n%s\n"
                (Ordinal.string_of @@ Ordinal.make i)
                (match cand_tag with
                | CandSol.Partial (Ident.Tvar key) ->
                    if config.check_part_sol_with_lbs then "LB_" ^ key else key
                | Total _ ->
                    if config.check_part_sol_with_lbs then "LB" else "-")
                (match cand_tag with
                | CandSol.Total true -> ""
                | _ -> "without sampling")
                (CandSol.str_of candidate)));
    let seeded = receive_bounds vs in
    round_undecided_unknowns := Set.Poly.empty;
    vs.VersionSpace.undecided_unknowns := Set.Poly.empty;
    Debug.print
    @@ lazy
         (VersionSpace.str_of_learned_clauses
            (PCSP.Problem.senv_of APCSP.problem)
            vs.learned_clauses);
    let clauses =
      Set.union (PCSP.Problem.clauses_of APCSP.problem)
      @@ Set.Poly.of_list
      @@ Hash_set.to_list vs.learned_clauses
    in
    let houdini =
      if
        (HoudiniConfig.Switch.declared_atoms config.houdini) && (not houdini_in_parallel)
        && not !houdini_done
      then (
        houdini_done := true;
        houdini_outcome ~record:(record_in vs) vs.fenv clauses)
      else `Not_applicable
    in
    match houdini with
    | `Solution sol ->
        Debug.print @@ lazy "*** a genuine solution is found (houdini): ";
        Debug.print @@ lazy (CandSol.str_of sol);
        Ok (State.Sat sol)
    | `Counterexamples _ | `Not_applicable ->
    (* only this round's own questions count, not the pre-pass's *)
    round_undecided_unknowns := Set.Poly.empty;
    let res =
      match config.cex_strategy with
      | AllExamples ->
          (* for each (possibly parametric) candidate solution, for each clause,
              generate a (possibly parametric) counterexample *)
          let is_hard =
            Clause.must_be_satisfied ~print:Debug.print
            @@ Map.key_set
            @@ PCSP.Problem.partial_sol_targets_of APCSP.problem
          in
          let rec iter examples = function
            | [] -> First examples
            | (cand, cand_tag) :: candidates -> (
                if RLCfg.config.enable && RLCfg.config.show_candidates then (
                  RLConfig.lock ();
                  Debug.print_stdout
                  @@ lazy
                       (sprintf "candidate: %s" @@ Yojson.Safe.to_string
                      @@ CandSol.to_yojson cand);
                  RLConfig.unlock ());
                let hard_clauses =
                  match cand_tag with
                  | CandSol.Partial pvar ->
                      let pvs =
                        Map.Poly.find_exn
                          (PCSP.Problem.dep_graph_of APCSP.problem)
                          pvar
                      in
                      Set.filter clauses ~f:(is_hard pvs)
                  | _ -> clauses
                in
                let find cand =
                  find_all_counterexamples
                    ~record:(fun ex sub ->
                      VersionSpace.record_derivation vs ex ~rule:"instance"
                        ~subst:(Some sub))
                    hard_clauses vs.fenv cand
                in
                let cexs = find cand in
                (* a total parametric candidate with no counterexample is a
                   solution under the parameter values its groups were proved
                   with, not as it stands (its parameters are free variables
                   of the answer): it is instantiated with them, and the
                   instance, which has no parameter, is what is validated again
                   and answered *)
                let cand, cexs =
                  match cand_tag with
                  | CandSol.Total _
                    when Set.is_empty cexs
                         && not (Map.Poly.is_empty (fst cand)) ->
                      let values = !param_values in
                      let sub =
                        Map.Poly.mapi (fst cand) ~f:(fun ~key ~data ->
                            match Map.Poly.find values key with
                            | Some t -> t
                            | None ->
                                Logic.ExtTerm.of_old_term
                                  (Logic.mk_old_dummy data))
                      in
                      let inst =
                        ( Map.Poly.empty,
                          Set.Poly.map (snd cand) ~f:(fun (b, t) ->
                              (b, Logic.Term.subst sub t)) )
                      in
                      (inst, find inst)
                  | _ -> (cand, cexs)
                in
                if RLCfg.config.enable then (
                  RLConfig.lock ();
                  let total = Set.length hard_clauses in
                  let num_unsat = Set.length cexs in
                  let num_sat = total - num_unsat in
                  Debug.print_stdout
                  @@ lazy
                       (sprintf "reward: %s/%s" (string_of_int num_sat)
                          (string_of_int total));
                  Out_channel.flush Out_channel.stdout;
                  RLConfig.unlock ());
                match cand_tag with
                | CandSol.Partial _ ->
                    if config.check_part_sol_with_lbs || Set.is_empty cexs then
                      (* if [check_part_sol_with_lbs] is false, the candidate is qualified as a partial solution if it satisfies the related clauses *)
                      (* ToDo: in this case, the candidate is guaranteed to be a genuine partial solution? *)
                      send_candidate_partial_solution vs cexs cand cand_tag
                        hard_clauses;
                    iter examples candidates
                | Total with_sampling ->
                    candidate_dump vs cand cexs;
                    if Set.is_empty cexs then Second cand
                    else (
                      (* diagnostic only, off unless its environment switch is
                         set: what this round's counterexamples refute the
                         candidate for, contents or indices *)
                      if PCSatCommon.RefutationCensus.on () then
                        PCSatCommon.RefutationCensus.report ~id vs.fenv
                          (CandSol.to_old cand)
                          (List.map (Set.to_list cexs) ~f:fst);
                      send_candidate_partial_solution vs cexs cand cand_tag
                        hard_clauses;
                      let examples' =
                        if with_sampling then
                          let unknowns =
                            Map.key_set @@ PCSP.Problem.senv_of APCSP.problem
                          in
                          Set.union examples
                          @@ Set.Poly.map cexs ~f:(fun (ex, srcs) ->
                              let ex' =
                                ExClause.normalize_params unknowns
                                @@ ExClause.normalize ex
                              in
                              VersionSpace.copy_derivation vs ~from:ex ~to_:ex';
                              (ex', srcs))
                        else examples
                      in
                      iter examples' candidates))
          in
          iter Set.Poly.empty candidates
      | ExamplesUpTo num_of_examples -> (
          (* for each clause,
              generate up to [num_of_examples] counterexamples that are not satisfied by as much candidates as possible *)
          (* assume candidates are non-parametric *)
          let examples, spurious_cands =
            Set.fold clauses ~init:(Set.Poly.empty, Set.Poly.empty)
              ~f:(fun (examples, spurious_cands) cl ->
                let examples', spurious_cands' =
                  find_common_counterexamples_for_clause
                    ~record:(fun ex sub ->
                      VersionSpace.record_derivation vs ex ~rule:"instance"
                        ~subst:(Some sub))
                    vs.fenv num_of_examples candidates cl
                in
                let examples' =
                  Set.Poly.map examples' ~f:(fun ex ->
                      (ex, Set.Poly.singleton (ClauseGraph.Clause cl, false)))
                in
                ( Set.union examples examples',
                  Set.union spurious_cands spurious_cands' ))
          in
          let is_genuine_solution cand = not @@ Set.mem spurious_cands cand in
          match
            List.find (List.map ~f:fst candidates) ~f:is_genuine_solution
          with
          | None -> First examples
          | Some cand -> Second cand)
    in
    (* the fixed point's counterexamples join this round's, when asked for *)
    let res =
      match (houdini, res) with
      | `Counterexamples cexs, First examples
        when config.houdini.feedback_counterexamples ->
          First (Set.union examples (normalize_counterexamples vs cexs))
      | _ -> res
    in
    (* the instances received seeds chose join this round's examples; the
       version space records them, so that an [unsat] can say whether the
       refuted example set held any.  Empty (and nothing done) unless a seed
       message arrived. *)
    let vs =
      match (seeded, vs.VersionSpace.seeded_examples, res) with
      | None, None, _ | _, _, Second _ -> vs
      | _, previous, First examples ->
          let incoming, trace, reads =
            match seeded with
            | Some (exs, t, r) -> (Set.Poly.map exs ~f:fst, t, r)
            | None -> (Set.Poly.empty, false, true)
          in
          let previous, trace, reads =
            match previous with
            | Some { seeded = exs; trace = t; synthesis_reads = r } ->
                (exs, t || trace, r && reads)
            | None -> (Set.Poly.empty, trace, reads)
          in
          let all = Set.union previous incoming in
          (* kept from synthesis: an instance this round (or a later one)
             also finds as an ordinary counterexample leaves the set, since
             synthesis must see it or it would propose the candidate it
             refutes again *)
          let all =
            if reads then all
            else Set.diff all (Set.Poly.map examples ~f:fst)
          in
          {
            vs with
            seeded_examples =
              Some { VersionSpace.seeded = all; trace; synthesis_reads = reads };
          }
    in
    let res =
      match (seeded, res) with
      | Some (seeded, _, _), First examples -> First (Set.union examples seeded)
      | _ -> res
    in
    (* A round that returns only the vacuous example has rejected the candidate
       and learnt nothing: the example set does not grow, so the next synthesis
       is asked the same question and proposes the same candidate.  Counting
       those is what lets the loop stop instead of repeating itself. *)
    let learnt_nothing exs =
      (not (Set.is_empty exs))
      && Set.for_all exs ~f:(fun (ex, _) ->
          Set.is_empty ex.ExClause.negative
          && Set.for_all ex.ExClause.positive ~f:(function
            (* the vacuous atom is [FCon] with no parameters and the
                     formula [true]; compared structurally, because an
                     [ExAtom] can hold a [Map.Poly] whose comparator is a
                     closure and [Stdlib.( = )] on one raises *)
            | ExAtom.FCon (params, phi) ->
                Map.Poly.is_empty params && Formula.is_true phi
            | _ -> false))
    in
    (match res with
    | First examples when learnt_nothing examples ->
        Int.incr fruitless_rounds;
        (* a fruitless round whose candidate list was rejected that way in an
           earlier round is a repeat: the same questions at the same budgets
           again.  Counted for the phase report; it decides nothing. *)
        let key = candidates_key candidates in
        let repeat = Hash_set.mem fruitless_keys key in
        Hash_set.add fruitless_keys key;
        vs.VersionSpace.undecided_unknowns := !round_undecided_unknowns;
        Common.PhaseTime.event "validation-fruitless";
        if repeat then Common.PhaseTime.event "validation-fruitless-repeat";
        Debug.print
        @@ lazy
             (sprintf
                "*** this round rejected the candidate and learnt nothing (%d \
                 in a row%s)"
                !fruitless_rounds
                (if repeat then ", a candidate rejected so before" else ""))
    | _ -> fruitless_rounds := 0);
    match res with
    | First _ when PCSatCommon.RecFunDynamic.has_pending () ->
        (* the dynamic encoding of counted recursive functions is armed and a
           clause it may encode was left undecided this round: end the loop
           with [unknown], after which that clause is encoded and the problem
           solved again (see [PCSatCommon.RecFunDynamic]), instead of
           rejecting the candidate with nothing learnt *)
        Debug.print
        @@ lazy
             "*** a clause applying a counted recursive function was left \
              undecided; ending the loop so that it is encoded";
        Ok State.Undecided
    | First _
      when match config.questions.give_up_after_undecided with
           | Some n -> !fruitless_rounds >= n
           | None -> false ->
        Debug.print
        @@ lazy
             (sprintf
                "*** %d rounds in a row rejected the candidate and learnt \
                 nothing; answering unknown rather than repeating"
                !fruitless_rounds);
        Ok State.Undecided
    | First examples ->
        Debug.print @@ lazy "******************************************";
        Debug.print @@ lazy "*** All the candidates are not genuine ***";
        Debug.print @@ lazy "******************************************\n";
        Debug.print @@ lazy "*** Counterexamples to the Candidate Solutions:";
        Debug.print
        @@ lazy
             (String.concat_map_set ~sep:";\n" ~f:(fst >> ExClause.str_of)
                examples);
        Debug.print @@ lazy "";
        Ok (State.of_examples vs examples)
    | Second sol ->
        Debug.print @@ lazy "*** a genuine solution is found: ";
        Debug.print @@ lazy (CandSol.str_of sol);
        Ok (State.Sat sol)

  let run_phase _iters e =
    if RLCfg.config.enable then (
      if RLCfg.config.show_elapsed_time then (
        RLConfig.lock ();
        Debug.print_stdout @@ lazy "begin validator";
        RLConfig.unlock ());
      let tm = Timer.make () in
      let res = State.Monad_infix.(Ok e >>=? validate) in
      if RLCfg.config.show_elapsed_time then (
        RLConfig.lock ();
        Debug.print_stdout @@ lazy (sprintf "end validator: %f" (tm ()));
        RLConfig.unlock ());
      res)
    else State.Monad_infix.(Ok e >>=? validate)
end

let make rl_config config pcsp =
  (module Make
            (struct
              let config = rl_config
            end)
            (struct
              let config = config
            end)
            (struct
              let problem = pcsp
            end) : ValidatorType)
