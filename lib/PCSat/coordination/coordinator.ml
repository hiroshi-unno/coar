open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open PCSatCommon
open Validation
open Resolution
open Synthesis
open Labeling

module Config = struct
  (** resolution and validation must be followed by Labeler *)
  type phase =
    | V of Validator.Config.t ext_file
    | R of Resolver.Config.t ext_file
    | S of Synthesizer.Config.t ext_file
    | L of Labeler.Config.t ext_file
    | P of phase * phase
  [@@deriving yojson]

  (** Deciding the clauses without an unknown first, as a problem with no
      unknown, through the whole zero-unknown verdict (its sequence
      instantiation, pins and retries).  Proved valid: they are dropped, and
      the loop runs on the rest.  Refuted: the problem is answered [unsat]
      with that refutation.  Undecided: the loop runs on the whole problem
      as without the pass.  Asked once per solve, before the sweep and the
      loop, when preprocessing leaves predicate variables and some clauses
      mention none of them. *)
  type prove_first =
    | No_prove_first
    | Prove_first of {
        beyond_arithmetic : bool; [@default false]
            (** a pre-check of the pass, decided from
                the sorts of the clauses' variables before anything is solved or
                forked: the pass runs only when some variable of the clauses
                without an unknown, free or bound, has a sort other than an
                integer, real, Boolean or bit-vector one (a sequence, an array, a
                datatype, a sort the input leaves open).  Why: what the pass
                buys over the loop's own validation query is the zero-unknown
                verdict's sequence instantiation and pins, which decided two
                clauses over a generic iterator's relations (open sorts,
                sequences under quantifiers) that a plain query never proved, so
                that no candidate was accepted; on clauses over arithmetic alone
                those devices have nothing to act on and the pass costs a fork
                and up to its budget.  [false]: the pass runs whenever such
                clauses exist, as before *)
        budget_ms : int option; [@default Some 60000]
            (** [Some ms] runs the pass
                in a forked copy of the process killed after [ms] milliseconds of
                wall clock, so it costs at most that (plus the fork) on an input
                where it decides nothing; a killed or failed copy is the undecided
                case.  A refutation found in the copy is answered [unsat] without
                a certificate, or, when one is asked for, the pass is run again in
                this process to build it.  [None]: the pass runs in this process
                with no bound but the ladder's own per-question budgets *)
        in_process_when_large : bool; [@default false]
            (** with [budget_ms = Some ms], the
                pass is run in this process, under a strict deadline of [ms],
                instead of in a forked copy whenever the fork's copy-on-write
                cost does not fit: when this process's major heap is larger than
                the least headroom ([memory.max - memory.current]) of its memory
                cgroups ([Common.ForkGuard.fork_fits]); since the shared memory
                budget ([Common.ForkGuard.fits]) this is what the pass does with
                the field off as well, so the field has no effect.  A forked OCaml copy
                writes every page of the live heap while its collector marks, so
                it can hold a second copy of the heap; past the headroom that
                copy is what a memory cap kills.  In process the pass asks the
                same questions; the deadline is read at phase boundaries, so it
                can overrun [ms] by one phase where the copy was killed on time,
                and an answer the deadline cuts is the undecided case, as a killed
                copy's is.  With no readable limit the copy is made as before *)
        within_deadline : bool; [@default true]
            (** with [budget_ms = Some ms],
                inside a nested solve bounded by a deadline (the finite
                instantiation of a quantified sort) the forked copy is killed at
                the earlier of [ms] and the deadline, and the pass is not run once
                the deadline has passed.  Why: the nested solve stops at its
                deadline only at a phase boundary, and this pass is one phase, so
                a nested solve given 10 s spent the pass's whole 60 s (an iterator
                adapter's loop, whose finite instance's unknown-free clauses the
                copy did not decide).  Only the copy's time is cut, so the switch
                can lose an answer the pass would have found after the deadline
                and never makes a wrong one *)
      }
  [@@deriving yojson]

  type unknown_free_clauses = {
    sweep : bool; [@default false]
        (** when preprocessing leaves predicate variables, first ask every
            clause that mentions none of them, piece by piece, under the
            budgets of [zero_unknown.budgets.quick_sweep] ((500, 5000) when that
            is [None]); a piece shown invalid refutes the problem at once,
            with its countermodel.  Asked once per solve, before the loop *)
    prove_first : prove_first;
        [@default
          Prove_first
            {
              beyond_arithmetic = false;
              budget_ms = Some 60000;
              in_process_when_large = false;
              within_deadline = true;
            }]
  }
  [@@deriving yojson]

  type t = {
    phase_list : phase list; [@default [ S (Common.Util.ExtFile.Filename "./config/pcsat/synthesizer/tbq_ar.json"); V (Common.Util.ExtFile.Filename "./config/pcsat/validator/nce.json"); L (Common.Util.ExtFile.Filename "./config/pcsat/labeler/sat1.json"); R (Common.Util.ExtFile.Filename "./config/pcsat/resolver/smt.json"); L (Common.Util.ExtFile.Filename "./config/pcsat/labeler/sat1.json") ]]
    rl_config : RLConfig.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/rl/disable.json"]
    verbose : bool; [@default false]
    build_synthesizer_on_first_use : bool; [@default true]
        (** build the synthesis phase when it is first run instead of with the
            other phases before the loop.  The loop's first iteration can ask
            the validator's pre-pass before any synthesis, and with
            [houdini.schedule = Parallel _] that pre-pass is raced in a forked copy at
            once; building the synthesizer first delays the copy by the whole
            build (the qualifier and template construction, 4-15 s on an input
            with a few dozen clauses over sequences, most of it outside the
            solver), although the copy needs it only if it hands back
            counterexamples for a later round.  With this on the copy is forked
            before the build, the process builds the synthesizer right after
            the fork, and the copy builds its own only if it runs a synthesis.
            The synthesizer is the same module either way; only when it is
            built, and so the order of fresh-name draws, changes *)
    eliminate_tot_preds : bool; [@default false]
        (** also solve away, before the loop, a [Tot u] predicate occurring
            only in clauses [P(t) => phi] (see [eliminate_fn_preds]); when
            off, a [Tot] predicate is always left to the templates *)
    zero_unknown : ZeroUnknownConfig.t;
        [@default Common.Util.config_default ZeroUnknownConfig.of_yojson "{}"]
        (** the zero-unknown verdict's ladder ([ZeroUnknownConfig]): the
            stages that decide a problem with no unknown left after
            preprocessing, and the clauses without an unknown asked
            first *)
    unknown_free_clauses : unknown_free_clauses;
        [@default Common.Util.config_default unknown_free_clauses_of_yojson "{}"]
        (** what is done, before the loop, with the clauses that mention no
            predicate variable when preprocessing leaves some (see
            [unknown_free_clauses]) *)
  }
  [@@deriving yojson]

  let rec load_ext_phase =
    let open Or_error in
    function
    | V cfg -> Validator.Config.load_ext_file cfg >>= fun cfg -> Ok (V cfg)
    | S cfg -> Synthesizer.Config.load_ext_file cfg >>= fun cfg -> Ok (S cfg)
    | R cfg -> Resolver.Config.load_ext_file cfg >>= fun cfg -> Ok (R cfg)
    | L cfg -> Labeler.Config.load_ext_file cfg >>= fun cfg -> Ok (L cfg)
    | P (phase1, phase2) ->
        load_ext_phase phase1 >>= fun phase1 ->
        load_ext_phase phase2 >>= fun phase2 -> Ok (P (phase1, phase2))

  let instantiate_ext_files cfg =
    let open Or_error in
    List.map ~f:load_ext_phase cfg.phase_list |> Result.all
    >>= fun phase_list ->
    RLConfig.load_ext_file cfg.rl_config >>= fun rl_config ->
    Ok { cfg with phase_list; rl_config }

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "Coordinator"
    let instantiate = instantiate_ext_files
  end)

  let str_of_phase = function
    | V _ -> "Validation"
    | S _ -> "Synthesis"
    | R _ -> "Resolution"
    | L _ -> "Labeling"
    | P _ -> "Parallel"

  module type ConfigType = sig
    val config : t
  end
end

(* Refuting a constraint by fixing the lengths of its free sequence variables
   lives in [SeqPin], where the validator can use it too. *)
(* The resource limit of a zero-unknown question asked in the ladder stage
   [phase] ([zero_unknown.budgets.stage_rlimits]): the first binding of
   [phase] in [stage_rlimits] when there is one, else [default] (the
   ladder-wide [zero_unknown.budgets.query_rlimit]).  Total; [stage_rlimits = []] gives
   [default] for every stage, so the field's default changes nothing.  Only the
   questions the ladder asks through its budgeted helper read it; a site
   inside such a question that sets the ladder-wide limit itself replaces the
   stage's limit with that one when the ladder-wide limit is set, and leaves
   it alone when it is [None]. *)
module LadderStageRlimit = struct
  let find ~stage_rlimits ~default phase =
    match List.Assoc.find stage_rlimits ~equal:String.equal phase with
    | Some r -> Some r
    | None -> default
end

(* The ladder's sequence-axiom fallback bound by a resource count
   ([zero_unknown.axioms.ladder_fallback]): [with_ (Some (units,
   kill_ms)) f] runs [f] with the fallback's questions under [units] and its
   budget replaced by [kill_ms] (each question's own budget still capping
   it); [with_ None f] is [f ()].  Both settings are per domain and
   restored on return and on raise.  Only an undecided answer is ever turned
   into a proof by the fallback, so the pair changes which undecided
   questions are proved, never what a proof says.  Both numbers are Z3's own
   parameters ([rlimit], [timeout]): asked in this process a check is bounded
   only where Z3 reads them, which it does not always do, and is killed only
   when the fallback asks in a forked copy
   ([zero_unknown.axioms.fork_fallbacks] or [z3.seq_axiom_fork]), at
   three times [kill_ms]. *)
module LadderSeqAxiomRlimit = struct
  let with_ pair f =
    match pair with
    | None -> f ()
    | Some (units, kill_ms) ->
        Z3Smt.Z3interface.with_seq_axiom_rlimit (Some units) @@ fun () ->
        Z3Smt.Z3interface.with_seq_axiom_fallback_base (Some kill_ms) f

  (* Which fallbacks get the pair, and with which count
     ([zero_unknown.axioms.ladder_fallback.scope],
     [zero_unknown.axioms.ladder_fallback.units_per_node]).

     [around_question ~refused_only ~per_node pair] is what is set around a
     whole ladder question: [pair] when neither refinement is on (every
     fallback the question asks, pooled ones inside [check_valid] included,
     gets it, as before), and nothing otherwise, the pair then being chosen
     per fresh question by [for_fallback].

     [for_fallback ~refused_only ~per_node ~only_attempt ~size pair] is the
     pair for the fallback of one fresh question of [size] nodes, where
     [only_attempt] says the solver was not asked the question itself:
     [None] (the process-wide wall-clock budget) when [pair] is [None], when
     [refused_only] holds and the solver was asked, or when [per_node = Some
     k] and [k * size] is below the pair's [units]; otherwise the pair, its
     count replaced by [k * size] when [per_node = Some k].  Total, and with
     both refinements off it returns [pair] itself, so that setting it inside
     [around_question]'s changes nothing. *)
  let around_question ~refused_only ~per_node pair =
    if refused_only || Option.is_some per_node then None else pair

  let for_fallback ~refused_only ~per_node ~only_attempt ~size pair =
    match pair with
    | None -> None
    | Some (units, kill_ms) -> (
        if refused_only && not only_attempt then None
        else
          match per_node with
          | None -> pair
          | Some k ->
              let scaled = k * size in
              if scaled >= units then Some (scaled, kill_ms) else None)
end

module NoUnknownSeqPin = SeqPin

(* Refuting a constraint by fixing a clause's free variables to a point and
   proving the clause false there lives in [ScalarPin]. *)
module NoUnknownScalarPin = ScalarPin

(* Refuting a constraint by fixing a clause's free relations to the finite
   relations its facts and laws generate lives in [RelationPin]. *)
module NoUnknownRelationPin = RelationPin

(** A formula as the conjunction of smaller validity questions.

   [pieces phi] is a list of formulas whose conjunction is equivalent to
   [phi] in every model, and none of which has a free variable [phi] lacks:
   a conjunction is split into its conjuncts and a disjunction distributed
   over its disjuncts' pieces, stopping (and keeping the formula whole) where
   the number of pieces would exceed [max_pieces].  Only [/\] and [\/] at the
   top are entered: a quantifier, a [let], an [ite] inside a term and an
   [<=>] are each one piece, so a binder is never moved across a piece.  So
   [phi] is valid exactly when every piece is, and a countermodel of one
   piece -- a model of its negation -- is a model of [not phi] as it stands,
   since the conjunction of the pieces is [phi] in that model too.  Both
   directions are what the callers rely on: every piece valid proves [phi],
   and one piece refuted refutes it.

   What it buys: a clause whose premise is a case split reads, in its
   disjunctive form, as [not premise \/ (not case1 /\ ... /\ not casen)], and
   a clause whose head is a conjunction as [not body \/ (c1 /\ ... /\ cn)].
   On a Rust-derived input the solver left a clause of the first shape, asked
   whole, undecided after 120 seconds, while its pieces, each instantiated on
   its own terms, were decided in under a second each; on the Creusot-form
   [Skip] adapter it left the goal clause of [Skip::next]'s [ensures], whose
   head has five conjuncts, undecided at 10 s on 3 of 4 seeds, while each
   [body => ci] was decided in at most 0.01 s. *)
module ClausePieces = PCSatCommon.ClausePieces

(* The question rewrites of the zero-unknown ladder, as the validity
   service's [QuestionRewrites] value: every clause asked has its reads of a
   concatenation split by index; its prefixes of a concatenation split too
   under [zero_unknown.rewrites.split_seq_prefix] unless
   [zero_unknown.rewrites.split_seq_prefix (Focus_only)] keeps that split to the
   instantiated forms; integer binders split at their [ite] thresholds by the
   solver interface, in force around the ladder's asks, under
   [zero_unknown.rewrites.split_int_binders_at_ite]; the implied factor equalities
   under [zero_unknown.rewrites.implied_factor_equalities].  No one-point
   pre-rewrite: the ladder's one-point form ([zero_unknown.rewrites.onepoint.split])
   is a later stage of its own, not a rewrite of every question. *)
let ladder_question_rewrites (config : Config.t) : Ast.QuestionRewrites.t =
  {
    onepoint = false;
    split_seq_reads = true;
    prefix_over_concat =
      (match config.zero_unknown.rewrites.split_seq_prefix with
      | Everywhere -> true
      | No_prefix_split | Focus_only -> false);
    int_binders =
      (if config.zero_unknown.rewrites.split_int_binders_at_ite then
         Ast.QuestionRewrites.In_solver_calls
       else Ast.QuestionRewrites.Off);
    implied_factor_equalities =
      config.zero_unknown.rewrites.implied_factor_equalities;
  }

(* The sweep of unknown-free clauses ([unknown_free_clauses.sweep]); the
   contract and why a refutation is sound are at [PCSatCommon.UnknownFreeSweep].
   Here the pieces are [ClausePieces.of_clause]'s when [split] is set. *)
module UnknownFreeSweep = struct
  include PCSatCommon.UnknownFreeSweep

  let sweep ~split ~expired ~ask formulas =
    sweep
      ~pieces:(fun c ->
        if split then match ClausePieces.of_clause c with [] -> [ c ] | ps -> ps
        else [ c ])
      ~expired ~ask formulas
end

(* The instantiation of sequence and integer binders that only strengthens a
   validity question lives in [SeqInstantiation], where the validator can
   use it too. *)
module NoUnknownSeqInst = SeqInstantiation

(* The ladder's process-wide switches, set from a coordinator configuration.
   [SeqInstantiation] and [Ast.Evaluator] keep them in refs whose module
   defaults are [false] (or [None]) whatever the configuration's default is,
   so a reader that runs before any setter sees a different instantiation
   from the configured one.  Every reader therefore runs the setters first: the
   zero-unknown verdict, the validator's Houdini pre-pass, and the solution
   checker's instance stage (which, without it, checked with whatever the
   last setter in the process -- or none -- had left).  Setting a switch
   changes which forms are built and which questions can be answered, never
   what an answer means.  The refs are process-wide: two instances with
   different configurations in one process still see the last setter's
   values. *)
module LadderSwitches = struct
  (* The process-wide switches of [Ast.Evaluator.elim_onepoint_and_split_binders]
     (and the contextual-ite extra form of [SeqInstantiation]), set from the
     ladder's configuration [z]; returns whether the
     contextual rule is applied in place and whether as an extra form, which
     are never both.  Each switch adds an equivalence to the rewrite, so it
     changes which questions a solver can answer, never what an answer
     means.  The head of this module says who calls it. *)
  let set_onepoint_rewrite_switches (z : ZeroUnknownConfig.t) =
    Ast.Evaluator.split_constructor_equations :=
      z.rewrites.split_constructor_equations;
    Ast.Evaluator.onepoint_array_reads :=
      z.rewrites.onepoint.array_reads;
    let contextual_in_place, contextual_extra =
      match z.rewrites.contextual_ite with
      | No_contextual_ite -> (false, false)
      | In_place -> (true, false)
      | As_extra_form -> (false, true)
    in
    Ast.Evaluator.contextual_ite := contextual_in_place;
    SeqInstantiation.contextual_ite_extra_form := contextual_extra;
    Ast.Evaluator.surjective_pairing :=
      (ZeroUnknownConfig.Switch.surjective_pairing z);
    Ast.Evaluator.surjective_pairing_nested :=
      (ZeroUnknownConfig.Switch.surjective_pairing_nested z);
    Ast.Evaluator.lift_spine_blocks := z.rewrites.lift_spine_blocks;
    (contextual_in_place, contextual_extra)

  (* [zero_unknown.budgets.reads_strict_deadline] for the two routes the ladder
     hands a sequence piece it left undecided (the cvc5 retry and the lemma
     route), which run outside its own questions: [strict_deadline_passed z]
     says a route is not to be tried, and [cap_by_strict_deadline z ms] is a
     try's budget [ms] cut to the time left.  With the field off they are
     [false] and [ms], so nothing changes *)
  let strict_deadline_passed (z : ZeroUnknownConfig.t) =
    z.budgets.reads_strict_deadline
    && PCSatCommon.SolveDeadline.expired_strict ()

  let cap_by_strict_deadline (z : ZeroUnknownConfig.t) ms =
    if z.budgets.reads_strict_deadline then
      Option.value ~default:ms (PCSatCommon.SolveDeadline.cap_ms_strict (Some ms))
    else ms

  (* The process-wide switches of [SeqInstantiation]'s witness instantiation,
     set from the ladder's configuration [z]; [verbose] is the coordinator's
     (it adds an exit tally of the integer-binder split); [print]
     traces the cvc5 retry of an undecided piece.  Setting a switch changes
     which instantiated forms are built, never what a proof of one means. *)
  let set_seq_instantiation_switches ?(print = fun (_ : string lazy_t) -> ())
      ~verbose (z : ZeroUnknownConfig.t) =
    (* with the ladder's integer-binder split on and [verbose], one stderr
       line at exit tallying the questions it rewrote: a diagnostic, so a
       plain run's output stays the answer *)
    if z.rewrites.split_int_binders_at_ite && verbose then
      Ast.IntBinderSplit.report_tallies ();
    SeqInstantiation.onepoint_split_forms :=
      z.rewrites.onepoint.split;
    SeqInstantiation.instantiate_element_binders :=
      z.seq_instantiation.element_binders;
    SeqInstantiation.instantiate_index_map_binders :=
      z.seq_instantiation.index_map_binders;
    SeqInstantiation.seq_array_view_candidates :=
      z.candidates.seq_array_view;
    SeqInstantiation.pointwise_array_witnesses :=
      z.candidates.pointwise_array;
    SeqInstantiation.pointwise_seq_literals :=
      z.candidates.pointwise_seq_literal;
    SeqInstantiation.witness_forms :=
      z.seq_instantiation.witness_forms;
    SeqInstantiation.single_index_map_witness_forms
    := z.seq_instantiation.single_index_map_witness_forms;
    SeqInstantiation.drop_array_hypotheses :=
      z.seq_instantiation.drop_array_hypotheses;
    SeqInstantiation.unwrap_embedded_formulas_before_instantiation
    := z.rewrites.unwrap_embedded_formulas;
    SeqInstantiation.skolemize_positive_universals_before_instantiation
    := z.rewrites.skolemize_positive_universals;
    SeqInstantiation.cancel_forced_sequence_binders_before_instantiation
    := z.rewrites.cancel_forced_sequence_binders;
    SeqInstantiation.offset_int_candidates
    := (ZeroUnknownConfig.Switch.offset_int_candidates z);
    SeqInstantiation.array_read_int_candidates
    := z.candidates.array_read_int;
    SeqInstantiation.index_map_shift_candidates
    := z.candidates.index_map.shift;
    SeqInstantiation.index_map_join_candidates
    := z.candidates.index_map.join;
    SeqInstantiation.literal_range_int_candidates
    := z.candidates.literal_range_int;
    SeqInstantiation.recfun_predecessor_int_candidates
    := z.candidates.recfun_predecessor_int;
    SeqInstantiation.nested_focus_forms
    := z.candidates.nested_focus_forms;
    SeqInstantiation.element_candidates_through_constructors
    := z.candidates.through_constructors;
    SeqInstantiation.bool_binder_candidates
    := z.candidates.bool_binder;
    SeqInstantiation.split_seq_prefix_over_concat
    := (ZeroUnknownConfig.Switch.split_seq_prefix_over_concat z);
    SeqInstantiation.split_seq_prefix_focus_only
    := (ZeroUnknownConfig.Switch.split_seq_prefix_focus_only z);
    SeqInstantiation.offset_int_candidates_chain_only
    := (ZeroUnknownConfig.Switch.offset_int_candidates_chain_only z);
    SeqInstantiation.chain_candidates_free_only
    := z.candidates.chain_free_only;
    SeqInstantiation.chain_concat_candidates
    := z.candidates.chain_concat;
    SeqInstantiation.chain_focus_forms
    := z.chains.focus.form;
    SeqInstantiation.chain_focus_push_witnesses
    := z.chains.focus.push_witnesses;
    SeqInstantiation.case_split_index_forms
    := (ZeroUnknownConfig.Switch.case_split_index_forms z);
    (* set only around the coordinator's own sequence instantiation, where
       its short-budget asker exists *)
    SeqInstantiation.index_case_ask := None;
    SeqInstantiation.index_case_max_size_ratio
    := (ZeroUnknownConfig.Switch.case_split_index_max_size_ratio z);
    SeqInstantiation.lazy_plain_form
    := z.seq_instantiation.lazy_plain_form;
    SeqInstantiation.matched_instance_forms
    := z.matched_instances.forms;
    SeqInstantiation.matched_instance_hyp_budget
    := z.matched_instances.hyp_budget;
    SeqInstantiation.matched_instance_aligned_hyps
    := z.matched_instances.aligned_hyps;
    SeqInstantiation.matched_instance_element_candidates
    := z.matched_instances.element;
    SeqInstantiation.matched_instance_chain_join_candidates
    := z.matched_instances.chain_join;
    SeqInstantiation.chain_join_direct_reads
    := z.chains.join.direct_reads;
    SeqInstantiation.chain_join_forms_first
    := z.chains.join.forms_first;
    SeqInstantiation.matched_instance_last_index_candidates
    := z.matched_instances.last_index;
    SeqInstantiation.matched_instance_collections_only
    := z.matched_instances.collections_only;
    SeqInstantiation.chain_join_focused
    := z.chains.join.focused;
    SeqInstantiation.assoc_concat_matching
    := z.matched_instances.assoc_open;
    SeqInstantiation.open_scalar_matches
    := z.matched_instances.assoc_open;
    SeqInstantiation.max_matched_form_size
    := z.matched_instances.max_form_size;
    SeqInstantiation.max_chain_join_focus_size
    := z.chains.join.max_focus_size;
    SeqInstantiation.ground_funapps_linear
    := z.seq_instantiation.ground_funapps_linear;
    SeqInstantiation.matched_bound_before_ranking
    := z.matched_instances.bound_before_ranking;
    SeqInstantiation.goal_directed_instances
    := z.matched_instances.goal_directed;
    SeqInstantiation.piece_max_nodes
    := z.seq_instantiation.max_nodes;
    SeqInstantiation.piece_max_int_input_nodes
    := z.seq_instantiation.max_int_input_nodes;
    SeqInstantiation.chain_assoc_match_forms
    := z.chains.assoc_match;
    SeqInstantiation.prepend_unit_candidates
    := z.candidates.prepend_unit;
    SeqInstantiation.pointwise_concat_candidates
    := z.candidates.pointwise_concat;
    SeqInstantiation.singleton_extension_candidates
    := z.candidates.singleton_extension;
    SeqInstantiation.uncapped_conjunction_pieces
    := z.pieces.uncapped_conjunctions;
    SeqInstantiation.share_premise_instances
    := z.pieces.share.premise_instances;
    SeqInstantiation.replay_piece_names
    := (ZeroUnknownConfig.Switch.replay_piece_fresh_names z);
    SeqInstantiation.group_open_pieces
    := (ZeroUnknownConfig.Switch.group_open_pieces z);
    SeqInstantiation.group_piece_forms
    := (ZeroUnknownConfig.Switch.group_piece_forms z);
    SeqInstantiation.lead_forms_before_grouping
    := (ZeroUnknownConfig.Switch.lead_forms_before_grouping z);
    SeqInstantiation.lead_forms_under_open_grouping
    := (ZeroUnknownConfig.Switch.lead_forms_under_open_grouping z);
    SeqInstantiation.lead_forms_for_unasked_groups
    := (ZeroUnknownConfig.Switch.lead_forms_for_unasked_groups z);
    SeqInstantiation.lead_forms_open_min_nodes
    := (ZeroUnknownConfig.Switch.lead_forms_under_open_grouping_min_nodes z);
    SeqInstantiation.share_piece_simplify
    := (ZeroUnknownConfig.Switch.share_piece_simplify z);
    SeqInstantiation.share_replayed_int_instances
    := z.pieces.share.replayed_int_instances;
    SeqInstantiation.share_deep_shapes
    := z.pieces.share.deep_shapes;
    SeqInstantiation.group_question_max_nodes
    := (ZeroUnknownConfig.Switch.group_question_max_nodes z);
    PCSatCommon.LemmaApplication.extended
    := (ZeroUnknownConfig.Switch.lemma_application_extended z);
    PCSatCommon.LemmaApplication.goal_first_probe
    := (ZeroUnknownConfig.Switch.lemma_goal_first_probe z);
    PCSatCommon.LemmaApplication.offer_read_maps
    := (ZeroUnknownConfig.Switch.lemma_read_maps z);
    PCSatCommon.LemmaApplication.offer_map_lengths
    := (ZeroUnknownConfig.Switch.lemma_map_lengths z);
    PCSatCommon.LemmaApplication.retry_with_laws
    := (ZeroUnknownConfig.Switch.lemma_law_retry z);
    PCSatCommon.LemmaApplication.keep_after_fact
    := (ZeroUnknownConfig.Switch.lemma_keep_hypotheses z);
    SeqInstantiation.lemma_before_retry
    := (ZeroUnknownConfig.Switch.lemma_application_before_cvc5 z);
    SeqInstantiation.lemma_after_form_timeout
    := (ZeroUnknownConfig.Switch.lemma_application_after_form_timeout z);
    SeqInstantiation.lemma_application_prover
    := Option.map (ZeroUnknownConfig.Switch.lemma_application_ms z) ~f:(fun ms piece ->
           (* at most the budget left to a caller that set one
              ([SeqInstantiation.with_last_attempt_budget]) *)
           match SeqInstantiation.last_attempt_ms ms with
           | None -> false
           | Some _ when strict_deadline_passed z ->
               (* past a strict deadline the lemma route is not tried, as
                  the ladder's own questions are not asked: an untried route
                  proves nothing, which leaves the piece open exactly as a
                  failed one does.  Without this the route's questions (a
                  dozen per piece) ran on for tens of seconds after a probe's
                  deadline had passed *)
               PCSatCommon.SolveDeadline.cut ();
               false
           | Some ms ->
           let ms = cap_by_strict_deadline z ms in
           Common.PhaseTime.with_phase "lemma-application" (fun () ->
               let outcome =
                 PCSatCommon.LemmaApplication.z3_outcome ~ms
                   ?rlimits:(ZeroUnknownConfig.Switch.lemma_application_rlimits z)
               in
               let law_outcome =
                 Option.map (ZeroUnknownConfig.Switch.lemma_law_retry_rlimits z)
                   ~f:(fun rl ->
                     PCSatCommon.LemmaApplication.z3_outcome ~ms ~rlimits:rl)
               in
               PCSatCommon.LemmaApplication.prove ~outcome ?law_outcome
                 ~trace:(fun r -> print @@ lazy ("[no-unknown verdict] " ^ Lazy.force r))
                 ~usable:(fun fact -> not (Z3Smt.Z3interface.may_not_return fact))
                 ~valid:(fun psi ->
                   match outcome psi with `Valid -> true | _ -> false)
                 piece));
    SeqInstantiation.true_forms_proved
    := z.external_.proof_shortcuts;
    PCSatCommon.Cvc5Proof.shortcuts
    := z.external_.proof_shortcuts;
    PCSatCommon.Cvc5Proof.rename_reserved
    := z.external_.cvc5_spelling.rename_reserved_symbols;
    PCSatCommon.Cvc5Proof.unindex_recursive
    := z.external_.cvc5_spelling.unindex_recursive_functions;
    SeqInstantiation.cvc5_on_undecided_form
    := (ZeroUnknownConfig.Switch.ladder_cvc5_on_undecided_form z);
    PCSatCommon.ScalarPin.binder_free_chain_bound
    := (ZeroUnknownConfig.Switch.pin_scalars_binder_free_chain_bound z);
    SeqInstantiation.undecided_piece_prover
    := Option.map (ZeroUnknownConfig.Switch.ladder_cvc5_retry_ms z) ~f:(fun ms phi ->
           (* the piece as the ladder's Z3 checks ask it: where
              [Z3interface.with_split_int_binders] is in force in this domain
              ([zero_unknown.rewrites.split_int_binders_at_ite]), its integer
              binders are split at their [ite] thresholds and the upper parts
              shifted to start at zero, and otherwise it is [phi] itself.  The
              rewrite is an equivalence in every model that adds no free
              variable, so cvc5's proof of it is a proof of [phi] *)
           match SeqInstantiation.last_attempt_ms ms with
           | None -> false
           | Some _ when strict_deadline_passed z ->
               (* as the lemma route below: an unasked retry proves nothing,
                  as an undecided one; cvc5 runs in a process of its own
                  and its budget is its own, so nothing else ends it *)
               PCSatCommon.SolveDeadline.cut ();
               false
           | Some ms ->
           let ms = cap_by_strict_deadline z ms in
           let phi = Z3Smt.Z3interface.split_int_binders_here phi in
           (* timed as its own phase: the retry runs cvc5 in a separate
              process, so its wait is otherwise charged to no named phase *)
           PCSatCommon.ValidityAsk.proved_by_cvc5
             ~trace:(fun r ->
               print @@ lazy ("[no-unknown verdict] cvc5 retry: " ^ r))
             {
               ms;
               rlimit = (ZeroUnknownConfig.Switch.ladder_cvc5_rlimit z);
               site = "ladder";
               phase = "cvc5-retry";
             }
             ~id:None
             (Z3Smt.Z3interface.fenv_reached_by (Ast.LogicOld.get_fenv ()) phi)
             phi)

  (* both setters, for a reader that does not need the contextual-ite pair *)
  let set ?print (config : Config.t) =
    ignore (set_onepoint_rewrite_switches config.zero_unknown : bool * bool);
    set_seq_instantiation_switches ?print ~verbose:config.verbose
      config.zero_unknown
end

module type CoordinatorType = sig
  val solve :
    ?witness:WitnessConfig.t ->
    ?oracle:PCSP.Problem.oracle ->
    PCSP.Problem.t ->
    State.output Or_error.t
end

(* raised by the zero-unknown verdict's ladder when
   [zero_unknown.budgets.reads_strict_deadline] is on and a strict solve deadline has
   passed; caught where the verdict starts, which answers [unknown] *)
exception Zero_unknown_deadline_passed

module Make (Cfg : Config.ConfigType) (MContext : Context.ContextType) :
  CoordinatorType = struct
  module type MUS = sig
    val run_phase : int -> State.u -> State.s Or_error.t
    val init : unit -> unit
  end

  module type MUU = sig
    val run_phase : int -> State.u -> State.u Or_error.t
  end

  module type MSU = sig
    val run_phase : int -> State.s -> State.u Or_error.t
    val houdini_before_synthesis : State.u -> State.u option
    val houdini_at_round_boundary : elapsed_s:float -> State.u -> State.u option
    val houdini_in_parallel : bool
    val houdini_parallel_prepass : State.u -> State.u option
    val houdini_seq_instantiation : bool
  end

  type phase_type =
    | US of (module MUS)
    | UU of (module MUU)
    | SU of (module MSU)

  type state_type = S of State.s | U of State.u

  let str_of_phase_type = function US _ -> "US" | UU _ -> "UU" | SU _ -> "SU"
  let str_of_state_type = function S _ -> "S" | U _ -> "U"
  let id = ref None

  (* numbers the ladder's questions written under COAR_DUMP_LADDER_QUESTIONS *)
  let ladder_question_dump_count = Atomic.make 0
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  (* the grouping counters of [zero_unknown.pieces.grouping], on stderr
     whenever that switch is on, so that a run shows that it was read and what
     the grouped questions did, without the verbose trace (which prints every
     form asked, megabytes each on the inputs the switch is for) *)
  module GroupDebug =
    Common.Debug.Make
      ((val Common.Debug.Config.(
              if (ZeroUnknownConfig.Switch.group_piece_forms config.zero_unknown) then enable
              else disable)))

  let set_onepoint_rewrite_switches () =
    LadderSwitches.set_onepoint_rewrite_switches config.zero_unknown

  let set_seq_instantiation_switches () =
    LadderSwitches.set_seq_instantiation_switches ~print:Debug.print
      ~verbose:config.verbose config.zero_unknown

  let build_phase pcsp rl_config phase =
    let open Config in
    let open Or_error in
    match phase with
    | V cfg ->
        ExtFile.unwrap cfg >>= fun cfg ->
        Ok
          (Common.PhaseTime.with_phase "build-V" (fun () ->
               SU (Validator.make rl_config cfg pcsp)))
    | R cfg ->
        ExtFile.unwrap cfg >>= fun cfg ->
        Ok
          (Common.PhaseTime.with_phase "build-R" (fun () ->
               UU (Resolver.make rl_config cfg pcsp)))
    | S cfg when config.build_synthesizer_on_first_use ->
        ExtFile.unwrap cfg >>= fun cfg ->
        (* the module the loop holds forces the build at its first use; the
           build includes [init], which the loop's own [init] call would
           otherwise have made before the first iteration *)
        let built =
          lazy
            (Common.PhaseTime.with_phase "build-S" (fun () ->
                 let (module M : MUS) = Synthesizer.make rl_config cfg pcsp in
                 Common.PhaseTime.with_phase "init-S" M.init;
                 (module M : MUS)))
        in
        Ok
          (US
             (module struct
               let run_phase i e =
                 let (module M : MUS) = Lazy.force built in
                 M.run_phase i e

               let init () = ()
             end))
    | S cfg ->
        ExtFile.unwrap cfg >>= fun cfg ->
        Ok
          (Common.PhaseTime.with_phase "build-S" (fun () ->
               US (Synthesizer.make rl_config cfg pcsp)))
    | L cfg ->
        ExtFile.unwrap cfg >>= fun cfg ->
        Ok
          (Common.PhaseTime.with_phase "build-L" (fun () ->
               UU (Labeler.make rl_config cfg pcsp)))
    | P (_phase1, _phase2) -> Or_error.unimplemented "build_phase"

  let last_version_space = ref None

  let str_of_phase_list n =
    config.phase_list
    |> String.concat_mapi_list ~sep:" >> " ~f:(fun i phase ->
        Config.str_of_phase phase |> if i = n then String.bracket else Fn.id)

  let print_status pcsp iter n =
    let header =
      "************** current phase of "
      ^ Ordinal.string_of (Ordinal.make iter)
      ^ " iteration **************"
    in
    Debug.print @@ lazy (header ^ "\n");
    Debug.print @@ lazy (str_of_phase_list n ^ "\n");
    Debug.print @@ lazy (String.init (String.length header) ~f:(fun _ -> '*'));
    (* [senv ⊆ dom(kind_map)] is maintained by hand and any
       [{ params with senv = ... }] can break it; a reader then either filters
       the drift silently or raises from [find_exn].  Reported at every phase
       boundary, which is the measurement to have before the two maps are
       merged into one. *)
    let missing =
      PCSP.Params.unknowns_without_kind (PCSP.Problem.params_of pcsp)
    in
    if Fn.non Set.is_empty missing then
      Debug.print
      @@ lazy
           (sprintf "[params] %d unknown(s) without a kind: %s"
              (Set.length missing)
              (String.concat_map_set ~sep:", " ~f:Ast.Ident.name_of_tvar missing))

  let app_phase messenger pcsp iters i e phase =
    let open Or_error in
    e >>= fun e ->
    Common.Messenger.receive_request messenger !id;
    (* remember the version space before every phase, so the evidence a
       phase records when it concludes [Unsat] is reachable even in the first
       iteration *)
    (match e with
    | U e when Fn.non State.is_end e ->
        last_version_space := Some (State.version_space_of e)
    | S e when Fn.non State.is_end e ->
        last_version_space := Some (State.version_space_of e)
    | _ -> ());
    (* a nested run past its deadline stops at this boundary with [Timeout],
       which every later phase passes through unchanged; a run that is not
       nested has no deadline and is untouched *)
    let e =
      match e with
      | U e' when Fn.non State.is_end e' && SolveDeadline.expired () ->
          U State.Timeout
      | S e' when Fn.non State.is_end e' && SolveDeadline.expired () ->
          S State.Timeout
      | _ -> e
    in
    (* the phase-time account's name for phase [i]: its kind in the
       configured list, lower-cased *)
    let timed f =
      Common.PhaseTime.with_phase
        (match List.nth config.phase_list i with
        | Some p -> String.lowercase (Config.str_of_phase p)
        | None -> "phase")
        f
    in
    match (e, phase) with
    | U e, US (module Phase : MUS) ->
        if Fn.non State.is_end e then (
          print_status pcsp iters i;
          Atomic.incr PhaseCount.synthesis);
        timed (fun () -> Phase.run_phase iters e) >>= fun e -> Ok (S e)
    | U e, UU (module Phase : MUU) ->
        if Fn.non State.is_end e then print_status pcsp iters i;
        timed (fun () -> Phase.run_phase iters e) >>= fun e -> Ok (U e)
    | S e, SU (module Phase : MSU) ->
        if Fn.non State.is_end e then (
          print_status pcsp iters i;
          Atomic.incr PhaseCount.validation);
        timed (fun () -> Phase.run_phase iters e) >>= fun e -> Ok (U e)
    | _ ->
        Error
          (Error.of_thunk (fun () ->
               sprintf
                 ("phase type error: apply %s phase to %s state.\n"
                ^^ "coordinator configuration may be broken\n"
                ^^ "Hint:\n e.g., any validator follows only synthesizer")
                 (str_of_phase_type phase) (str_of_state_type e)))

  let update_context_version () =
    match !last_version_space with
    | None -> ()
    | Some vs -> (
        match MContext.context.version with
        | None -> assert false
        | Some version ->
            Context.set_version MContext.context
            @@ Context.version_of version vs)

  (* the typed payload of [Unsat]: the recorded witness as a refutation
     ([PCSP.Refutation]) *)
  (* The witness terms of a countermodel refutation, as a suspension of
     [CountermodelWitness.find] over [phi] and [model] (see
     [UnsatWitness.Countermodel] for where it may be forced).  The function
     environment is read now, at the refutation, and not when the
     suspension is forced, so the search reads the formula in the
     environment it was refuted in.  The event [countermodel-witness-deferred]
     counts the refutations at which the search would have run eagerly. *)
  let lazy_witnesses ~timeout phi model =
    let fenv = Ast.LogicOld.get_fenv () in
    Common.PhaseTime.event_here "countermodel-witness-deferred";
    lazy (CountermodelWitness.find ~fenv ~timeout phi model)

  let payload_of w = PCSP.Problem.Proof (UnsatWitness.to_refutation w)

  let rec main_loop ~pcsp sol_eliminated messenger
      (f : int -> State.u -> state_type Or_error.t) num_iters e =
    let open Or_error in
    update_context_version ();
    if config.verbose then Context.show_graph ~id:!id MContext.context.version;
    Common.Messenger.receive_request messenger !id;
    e >>= fun e ->
    f num_iters e >>= function
    | U (State.Sat cand) ->
        (* a census line, read by nothing: the units of the solution's bodies
           whose parameter positions the clauses do not relate (both forms of
           the relation), which a template under [extra_quals.related_positions]
           could not have built from a generated qualifier *)
        (if Option.is_some (Sys.getenv "COAR_RELPOS_CENSUS") then
           try
             let clauses =
               match PCSP.Problem.clauses_of_opt pcsp with
               | None -> []
               | Some cls ->
                   Set.to_list
                   @@ Ast.ClauseSet.to_old_clause_set
                        (PCSP.Problem.senv_of pcsp) cls
             in
             let binds =
               Set.to_list (snd (Ast.CandSol.to_old cand))
             in
             List.iter [ false; true ] ~f:(fun whole_clause ->
                 let rel = Ast.RelatedPositions.compute ~whole_clause clauses in
                 List.iter (Ast.RelatedPositions.unrelated_units rel binds)
                   ~f:(fun (p, n, bad) ->
                     eprintf "[relpos-census] whole=%b %s units=%d unrelated=%d%s\n%!"
                       whole_clause (Ast.Ident.name_of_pvar p) n
                       (List.length bad)
                       (String.concat
                          (List.map (List.take bad 3) ~f:(fun u ->
                               " | " ^ Ast.LogicOld.Formula.str_of u)))))
           with exn_ when not (Common.Timer.is_async exn_) ->
             eprintf "[relpos-census] failed: %s\n%!" (Exn.to_string exn_));
        Ok
          ( PCSP.Problem.extend_sol
              (PCSP.Problem.Sat (Ast.CandSol.to_subst cand))
              sol_eliminated,
            {
              State.num_cegis_iters = num_iters;
              unsat_witness = None;
              kind_certificates =
                (match !last_version_space with
                | Some vs ->
                    Map.Poly.of_alist_exn
                      (Hashtbl.to_alist vs.VersionSpace.kind_certs)
                | None -> Map.Poly.empty);
            } )
    | U State.Unsat ->
        (* examples chosen by received ground seeds: with their sender's
           trace, how many the refuted example set held *)
        (match !last_version_space with
        | Some
            ({
               VersionSpace.seeded_examples =
                 Some { seeded; trace = true; _ };
               _;
             } as vs) ->
            let held =
              let exs = VersionSpace.examples_of vs in
              Set.count seeded ~f:(Set.mem exs)
            in
            Out_channel.output_string stderr
              (sprintf
                 "ground-seeds: unsat with %d of the %d seeded examples held\n"
                 held (Set.length seeded));
            Out_channel.flush stderr
        | _ -> ());
        let unsat_witness =
          Option.bind !last_version_space ~f:(fun vs ->
              Option.map !(vs.VersionSpace.unsat_witness) ~f:(fun w ->
                  { w with UnsatWitness.problem = Some pcsp }))
        in
        Option.iter unsat_witness ~f:(fun w ->
            Debug.print @@ lazy (UnsatWitness.str_of ~force:false w);
            Debug.print
            @@ lazy
                 ("payload: "
                 ^ PCSP.Refutation.str_of (UnsatWitness.to_refutation w)));
        Ok
          ( PCSP.Problem.Unsat (Option.map unsat_witness ~f:payload_of),
            {
              State.num_cegis_iters = num_iters;
              unsat_witness;
              kind_certificates = Map.Poly.empty;
            } )
    | U (State.Continue _ as e') ->
        let vs = State.version_space_of e' in
        last_version_space := Some vs;
        (* printed at the end of each round rather than at exit, because a run
           that is killed at its budget never reaches an exit handler and these
           are wanted precisely on the runs that do not finish *)
        (let pos, neg, und =
           PCSatCommon.VersionSpace.pos_neg_und_examples_of vs
         in
         (* how many of the positives are the vacuous [( => true)] validation
            returns when it can neither confirm nor refute a clause: those
            record that a round decided nothing rather than any fact about the
            problem *)
         let vacuous =
           Set.count pos ~f:(fun cl ->
               Set.exists cl.Ast.ExClause.positive ~f:Ast.ExAtom.is_vacuous)
         in
         PCSatCommon.GeneralityMonitor.version_space ~pos:(Set.length pos)
           ~neg:(Set.length neg) ~und:(Set.length und) ~vacuous);
        PCSatCommon.GeneralityMonitor.report ~round:num_iters (fun l ->
            Debug.print_stdout l);
        PCSatCommon.GeneralityMonitor.reset ();
        (* a round without an answer: a nested solve's shorter budget for
           the rounds after its first takes effect here *)
        PCSatCommon.SolveDeadline.round_ended ();
        main_loop ~pcsp sol_eliminated messenger f (num_iters + 1) (Ok e')
    | U State.Timeout ->
        Ok
          ( PCSP.Problem.Timeout,
            {
              State.num_cegis_iters = num_iters;
              unsat_witness = None;
              kind_certificates = Map.Poly.empty;
            } )
    | U (State.OutSpace ps) ->
        Ok
          ( PCSP.Problem.OutSpace ps,
            {
              State.num_cegis_iters = num_iters;
              unsat_witness = None;
              kind_certificates = Map.Poly.empty;
            } )
    (* The validator could not decide a clause, so the candidate was neither
       confirmed nor refuted and the round learnt nothing.  That is not a
       refutation and not a solution: it is [unknown], which is an ordinary
       answer here. *)
    | U State.Undecided ->
        Ok
          ( PCSP.Problem.Unknown,
            {
              State.num_cegis_iters = num_iters;
              unsat_witness = None;
              kind_certificates = Map.Poly.empty;
            } )
    | S _ -> Error (Error.of_thunk (fun () -> ""))

  (* The payload is the reason, stated in the unsat witness. *)
  exception NoSolution of string

  let solve =
    let module Z3interface =
      Z3Smt.Z3interfaceNew.Make (Z3Smt.Z3interfaceNew.ExtTerm) in
    fun senv phi ->
      Common.PhaseTime.with_phase "fresh-ctx-check" (fun () ->
          Z3interface.check_sat [ phi ] senv (Z3.mk_context []))

  (* [witnesses_of_game ~nondet ~is_sat ~neg_formula ~lose phi] plays the
     strategy-improvement game on [phi], which is the NEGATION of the closed
     formula [forall u. exists v. body] (so the SAT player of [phi] is the
     refuter).  It answers [`Refuted] when the refuter wins, i.e. when
     [forall u. exists v. body] is false; [`Witnesses sub] when the other player
     wins and its strategy could be turned into terms, [sub] mapping each
     existential variable that has a strategy to (its scope, a term over the
     universal variables alone -- the earlier existentials are substituted
     away); and [`Undecided] when the winning strategy could not be turned into
     terms.  The two theories' game modules have distinct types, so the module's
     entry points are passed in. *)
  let witnesses_of_game ~nondet ~is_sat ~neg_formula ~lose phi =
    let p, s = nondet solve phi in
    if is_sat p then `Refuted
    else
      let f = neg_formula phi in
      let fml, chc, det, params = lose [] s f in
      let chc =
        (Map.Poly.empty, Ast.Logic.ExtTerm.imply_of fml (Ast.Logic.BoolTerm.mk_bool false))
        :: chc
      in
      let problem =
        PCSP.Problem.of_formulas
          ~params:(PCSP.Params.make @@ Map.of_list_exn params)
        @@ Set.Poly.of_list chc
      in
      match PCSP.ForwardPropagate.solve problem with
      | Ok (PCSP.Problem.Sat subs) ->
          let ds =
            Map.Poly.map det ~f:(fun (senv, t) ->
                (senv, Ast.Logic.ExtTerm.subst subs t))
          in
          `Witnesses
            (Map.Poly.of_alist_exn
            @@ List.map (Map.Poly.to_alist ds) ~f:(fun (x, (senv, t)) ->
                let t =
                  fix
                    ~f:(Ast.Logic.Term.subst (Map.Poly.map ds ~f:snd))
                    ~equal:Stdlib.( = ) t
                in
                (x, (senv, t))))
      | _ -> `Undecided

  (* [eliminate_fn_preds pcsp] solves away, before the CEGIS loop, every
     predicate [P] that occurs only in clauses of the form [P(t) => phi] (one
     negative literal, no positive one) and nowhere else -- neither as an atom
     nor inside a pure part of any other clause.  It returns the eliminated
     predicates' solutions and the problem without [P] and its clauses.

     Write [body(x)] for the conjunction over [P]'s clauses of
     [forall y. (t = x) => phi].  A predicate of kind FN is eliminated by
     deciding [forall x. exists r. body(x, r)], [r] its last position; with
     [eliminate_tot_preds] set, one of kind [Tot u] by deciding
     [forall u. exists v. body(u, v)], [v] the positions not in [u].

     Soundness, for [Tot u] (FN is the case [u] = all but the last together
     with single-valuedness, which a witness FUNCTION's graph also has):
     - [sat]: the game's winning strategy gives a term [w(u)] for every [v],
       and [P(u, v) := v = w(u)] is total (every [u] has the point [w(u)]) and
       every point of it satisfies [body], hence every clause of [P]: a clause
       [forall y. P(t) => phi] meets [P(t)] only at [t = (u, w(u))], where
       [body] instantiated at [y] gives [phi].  [P] occurs nowhere else, so the
       other clauses are unaffected.
     - [unsat]: if some total [P] satisfies [P]'s clauses, then for each [u]
       totality gives a [v] with [P(u, v)], every clause instance with
       [t = (u, v)] then forces [phi], so [body(u, v)] holds and
       [forall u. exists v. body] is true.  So the refuter winning means no
       total [P] satisfies [P]'s clauses alone, and since the whole problem
       only adds clauses, it has no solution either.  This needs [body] to BE
       the meaning of [P]'s clauses: it may not mention another unknown (a
       pure part of [P]'s own clauses mentioning one would be read as a fixed
       formula, quantified by nothing) and [P] may not occur in a pure part
       of any clause.  Both are checked below, for both kinds.  The game's
       readers would not save an unchecked case: an applied unknown makes them
       decline, but a nullary numeric one reads as a free variable, which the
       game's solver cannot encode, and the solve stopped with an uncaught
       exception instead of an answer.
     [P]'s solution is returned with the problem, so an unknown whose
     solution a caller wants kept is not lost by its elimination here.
     The quantifier eliminations and simplifications applied to [body] are
     equivalences, and a [None] from either theory's reader or an undecided
     game keeps the clauses for the loop, which is only incompleteness.
     An FN predicate with a Boolean result and a quantifier-free [body] is
     decided without the game, by [eliminate_bool_fn_pred]. *)
  (* [eliminate_bool_fn_pred ~cls ~tvar ~args ~univ ~r body] is the
     elimination of an FN predicate [tvar] whose result [r] is Boolean, with
     [args] its parameters ([univ] and then [r]) and [body] quantifier-free.
     The strategy game cannot play it: its linear-arithmetic readers take no
     Boolean variable, so such a predicate was always left to the CEGIS loop,
     where the template of a Boolean function of no non-Boolean argument has
     no candidate at all, and even [P(b) => b] went unanswered.  None is
     needed: a Boolean has two values, so
       [forall univ. exists r. body]  iff  [forall univ. body[true] \/ body[false]],
     which is one validity question, and its winning strategy is
     [r := body[true]].
     - Valid: [P(univ, r) := (r <=> body[true])] is total and single-valued,
       and each of its points satisfies [body] (at [r = true] by definition,
       at [r = false] because [body[true]] fails there, so [body[false]]
       holds), hence every clause of [P], as [eliminate_fn_preds] argues.
     - Invalid: the refutation is [eliminate_fn_preds]'s, provided the
       countermodel is a real point.  That holds only on a formula without
       interpretation-dependent terms, so it is taken only when the question,
       its Boolean universals expanded into both values, is read by the
       game's linear integer or real reader -- the fragment whose verdicts
       the game itself trusts; elsewhere an invalid answer is only [unknown].
     - Anything else keeps the clauses for the loop (incompleteness only).
     Returns [First cls] (kept) or [Second (tvar, solution)]; raises
     [NoSolution] on a refutation. *)
  let eliminate_bool_fn_pred ~cls ~tvar ~args ~univ ~r body =
    let open Ast in
    let open Ast.LogicOld in
    let at x b phi = Formula.subst (Map.Poly.singleton x (T_bool.make b)) phi in
    let b_true = at r true body in
    let question = Formula.mk_or b_true (at r false body) in
    let in_linear_fragment () =
      let bools, others = List.partition_tf univ ~f:(snd >> Term.is_bool_sort) in
      let phi =
        List.fold bools ~init:question ~f:(fun phi (x, _) ->
            Formula.mk_and (at x true phi) (at x false phi))
      in
      let t =
        Logic.ExtTerm.of_old_formula @@ Evaluator.simplify
        @@ Formula.mk_forall_if_bounded others phi
      in
      Option.is_some (StratSynth.LIA.formula_of_term_with_constants t)
      || Option.is_some (StratSynth.LRA.formula_of_term_with_constants t)
    in
    match
      Z3Smt.Z3interface.check_valid ~timeout:(Some 10_000) ~id:None
        (get_fenv ()) question
    with
    | `Valid ->
        Second
          ( tvar,
            Logic.Term.mk_lambda
              (List.map args ~f:(fun (x, s) -> (x, Logic.ExtTerm.of_old_sort s)))
            @@ Logic.ExtTerm.of_old_formula
            @@ Formula.eq (Term.mk_var r T_bool.SBool) (T_bool.of_formula b_true)
          )
    | `Invalid _ when in_linear_fragment () ->
        raise
          (NoSolution
             "an FN predicate with a Boolean result cannot be total")
    | _ -> First cls

  (* [eliminate_term_fn_pred ~cls ~lst ~tvar ~args ~univ ~r ~sort body] is the
     elimination of an FN predicate [tvar] whose result [r] has a datatype, an
     array or a bit-vector sort [sort], with [args] its parameters ([univ] and
     then [r]), [lst] its clauses (each [P(ts) => phi], one negative atom and
     nothing else) and [body] their meaning, quantifier-free, over [args]
     (the eliminated form, or the one-point reading of the clauses where the
     elimination left a binder).
     The strategy game reads linear integer or real arithmetic only, and the
     CEGIS loop's templates for these sorts cannot express most witnesses (an
     array template is a constant array, a datatype template's leaves are the
     arguments themselves), so such a predicate went unanswered even when its
     clauses name the witness, as in [P(x, o) => is-some(o) /\ val(o) = x + 1].
     The question [forall univ. exists r. body] is quantified, and Z3 may not
     return on it whatever its budget, so it is never asked.  Only
     quantifier-free questions are, each with a budget:
     - [body] unsatisfiable: no [(univ, r)] satisfies [body] in any model of
       the theory under any interpretation of its underspecified terms (Z3
       reads a selector applied to the wrong constructor as an uninterpreted
       application, so its [unsat] covers every interpretation).  Sorts are
       non-empty, so any [univ] has no [r], and the refutation of
       [eliminate_fn_preds] applies: no total [P] satisfies [P]'s clauses.
       This is the validity of [not body], the sufficient half of the
       refutation; an invalid [forall univ. exists r. body] whose countermodel
       needs a particular [univ] is not detected and keeps the clauses.
     - Otherwise candidate witness terms [w] over [univ] are read from [body]
       and from Z3's model of it -- a quantifier-free projection restricted to
       definitions: [r = t], or a field of [r] isolated from a linear
       integer equation with coefficient 1 or -1; for a datatype, the constructor [c] of a tester
       [is-c(r)] or of [r]'s model value, with each field the [t] of a
       [sel(r) = t] or else the model value's field; for an array, the stores
       [select(r, i) = t] over [r]'s model value or a constant array -- each
       [t] and [i] free of [r] and mentioning only [univ].  The first [w] such
       that [P(ts) := last ts = w(init ts)] makes every clause of [lst] valid
       gives [P(univ, r) := r = w(univ)], which is total and single-valued;
       [P] occurs nowhere else ([eliminate_fn_preds] checks it), so the other
       clauses are unaffected.  Each check is the clause itself with [P]
       replaced, so it does not rest on [body]'s quantifier elimination.
       Validity is asked of Z3 with underspecified terms uninterpreted, so the
       solution holds in every model under every interpretation.
     - Anything else -- no candidate checks, a question not decided within
       its budget, a clause whose pure part is quantified -- keeps the clauses
       for the loop exactly as before (incompleteness only).
     Returns [First cls] (kept) or [Second (tvar, solution)]; raises
     [NoSolution] on a refutation. *)
  let eliminate_term_fn_pred ~cls ~lst ~tvar ~args ~univ ~r ~sort body =
    let open Ast in
    let open Ast.LogicOld in
    let fenv = get_fenv () in
    let univ_vars = Set.Poly.of_list (List.map univ ~f:fst) in
    let over_univ t = Set.is_subset (Term.tvs_of t) ~of_:univ_vars in
    let is_r = function
      | Term.Var (x, _, _) -> Ident.tvar_equal x r
      | _ -> false
    in
    let model_value =
      match
        Z3Smt.Z3interface.check_sat ~timeout:(Some 10_000) ~id:None fenv
          [ body ]
      with
      | `Unsat -> `Unsat
      | `Sat model ->
          `Value
            (List.find_map model ~f:(fun ((x, _), v) ->
                 if Ident.tvar_equal x r then
                   Option.filter v ~f:(fun t -> Set.is_empty (Term.tvs_of t))
                 else None))
      | _ -> `Value None
      | exception exn when not (Common.Timer.is_async exn) -> `Value None
    in
    match model_value with
    | `Unsat ->
        raise
          (NoSolution
             "an FN predicate whose clauses no value of its result satisfies \
              cannot be total")
    | `Value model_value -> (
        (* [body] has been through quantifier elimination and simplification,
           which may rewrite [val(o) = x + 1] into two strict inequalities, so
           the clauses' own pure parts are read as well, each over [args]
           when its atom's arguments are distinct variables *)
        let atoms =
          let pures =
            List.filter_map lst ~f:(fun (_, _, ns, phi) ->
                let _, _, ts, _ = Atom.let_pvar_app @@ Set.choose_exn ns in
                match
                  Option.all
                  @@ List.map ts ~f:(function
                    | Term.Var (x, _, _) -> Some x
                    | _ -> None)
                with
                | Some xs
                  when not (List.contains_dup ~compare:Stdlib.compare xs) ->
                    Some
                      (Formula.subst
                         (Map.Poly.of_alist_exn
                         @@ List.map2_exn xs args ~f:(fun x (y, s) ->
                             (x, Term.mk_var y s)))
                         phi)
                | _ -> None)
          in
          List.concat_map (body :: pures) ~f:(fun phi ->
              let pos, neg = Formula.atoms_of phi in
              Set.to_list (Set.union pos neg))
        in
        (* [(lhs, t)] for each equality [lhs = t] of [body] with [t] over
           [univ] alone *)
        let defs =
          List.concat_map atoms ~f:(function
            | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) ->
                (if over_univ t2 then [ (t1, t2) ] else [])
                @ if over_univ t1 then [ (t2, t1) ] else []
            | _ -> [])
        in
        (* and [(s, e)] for each integer equation that, read with a field
           [s] of [r] ([sel(r)] or [select(r, i)]) as its unknown, is linear in
           [s] with coefficient 1 or -1 and solves to [s = e]: the normalized
           [0 = -1 - x + val(o)] gives [val(o) = x + 1] *)
        let defs =
          let fields_of t =
            let acc = ref [] in
            ignore
            @@ Term.map_term true t ~f:(fun s ->
                (match s with
                | Term.FunApp (T_dt.DTSel _, [ a ], _)
                | Term.FunApp (T_array.ASelect _, [ a; _ ], _)
                  when is_r a ->
                    acc := s :: !acc
                | _ -> ());
                s);
            !acc
          in
          defs
          @ List.concat_map atoms ~f:(function
            | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _)
              when Term.is_int_sort (Term.sort_of t1) ->
                let t1 = Term.map_term true t1 ~f:Fn.id
                and t2 = Term.map_term true t2 ~f:Fn.id in
                List.filter_map
                  (List.dedup_and_sort ~compare:Stdlib.compare
                     (fields_of t1 @ fields_of t2))
                  ~f:(fun s ->
                    let z = Ident.mk_fresh_tvar () in
                    let abs =
                      Term.map_term true ~f:(fun t ->
                          if Stdlib.(t = s) then Term.mk_var z T_int.SInt
                          else t)
                    in
                    match ArrayPointwise.solve_for z (abs t1) (abs t2) with
                    | Some e when over_univ e -> Some (s, e)
                    | _ -> None)
            | _ -> [])
        in
        let direct =
          List.filter_map defs ~f:(fun (lhs, t) ->
              if is_r lhs then Some t else None)
        in
        let structural =
          match sort with
          | T_dt.SDT dt ->
              let testers =
                List.filter_map atoms ~f:(function
                  | Atom.App (Predicate.Psym (T_dt.IsCons (name, _)), [ t ], _)
                    when is_r t ->
                      Some name
                  | _ -> None)
              in
              let of_model =
                match model_value with
                | Some (Term.FunApp (T_dt.DTCons (name, _, _), ts, _)) ->
                    Some (name, ts)
                | _ -> None
              in
              List.dedup_and_sort ~compare:String.compare
                (testers @ Option.to_list (Option.map of_model ~f:fst))
              |> List.filter_map ~f:(fun name ->
                  match Datatype.look_up_cons dt name with
                  | None -> None
                  | Some cons ->
                      let model_args =
                        match of_model with
                        | Some (n, ts) when String.equal n name -> Some ts
                        | _ -> None
                      in
                      let fields =
                        List.mapi (Datatype.sels_of_cons cons) ~f:(fun i sel ->
                            let sname = Datatype.name_of_sel sel in
                            match
                              List.find_map defs ~f:(fun (lhs, t) ->
                                  match lhs with
                                  | Term.FunApp (T_dt.DTSel (s, _, _), [ a ], _)
                                    when String.equal s sname && is_r a ->
                                      Some t
                                  | _ -> None)
                            with
                            | Some t -> Some t
                            | None ->
                                Option.bind model_args ~f:(fun ts ->
                                    List.nth ts i))
                      in
                      Option.map (Option.all fields) ~f:(T_dt.mk_cons dt name))
          | T_array.SArray (si, se) ->
              let writes =
                List.filter_map defs ~f:(fun (lhs, t) ->
                    match lhs with
                    | Term.FunApp (T_array.ASelect _, [ a; i ], _)
                      when is_r a && over_univ i ->
                        Some (i, t)
                    | _ -> None)
              in
              if List.is_empty writes then []
              else
                List.map
                  (Option.to_list model_value
                  @ [ T_array.mk_const_array si se (Term.mk_dummy se) ])
                  ~f:(fun base ->
                    List.fold writes ~init:base ~f:(fun a (i, e) ->
                        T_array.mk_store si se a i e))
          | _ -> []
        in
        let candidates =
          List.take
            (List.filter ~f:over_univ
            @@ direct @ structural @ Option.to_list model_value)
            8
        in
        let satisfies w =
          List.for_all lst ~f:(fun (_, _, ns, phi) ->
              Formula.is_quantifier_free phi
              &&
              let _, _, ts, _ = Atom.let_pvar_app @@ Set.choose_exn ns in
              let tu, tr = List.rest_last ts in
              let sub =
                Map.Poly.of_alist_exn
                @@ List.map2_exn univ tu ~f:(fun (x, _) t -> (x, t))
              in
              match
                Z3Smt.Z3interface.check_valid ~timeout:(Some 2_000) ~id:None
                  fenv
                  (Formula.mk_imply (Formula.eq tr (Term.subst sub w)) phi)
              with
              | `Valid -> true
              | _ -> false
              | exception exn when not (Common.Timer.is_async exn) -> false)
        in
        match List.find candidates ~f:satisfies with
        | None -> First cls
        | Some w ->
            Second
              ( tvar,
                Logic.Term.mk_lambda
                  (List.map args ~f:(fun (x, s) ->
                       (x, Logic.ExtTerm.of_old_sort s)))
                @@ Logic.ExtTerm.of_old_formula
                @@ Formula.eq (Term.mk_var r sort) w ))

  let eliminate_fn_preds pcsp =
    let clauses = PCSP.Problem.clauses_of pcsp in
    let unknowns = Map.key_set (PCSP.Problem.senv_of pcsp) in
    let eliminable p =
      PCSP.Problem.is_fn_pred pcsp p
      || (config.eliminate_tot_preds && PCSP.Problem.is_tot_pred pcsp p)
    in
    let cls1, cls2 =
      Set.partition_tf clauses ~f:(fun (_uni_senv, ps, ns, _phi) ->
          Set.is_empty ps && Set.is_singleton ns
          && eliminable @@ Ast.Logic.Term.pvar_of_atom @@ Set.choose_exn ns)
    in
    let pvs2 =
      (* [ClauseSet.pvs_of] reads only the atom sets, so an unknown applied
         inside a clause's *pure* part is invisible to it -- and this decides
         whether an FN predicate is constrained anywhere else before it is
         solved away by strategy synthesis below.  One that occurs elsewhere
         only in a pure part would be solved ignoring that constraint, which is
         the shape of a bug the eliminator itself had: a predicate applied only
         in a pure part looked one-sided and was eliminated although the pure
         part still constrained it.  The pure parts are added here;
         a predicate counted that should not be only costs an elimination. *)
      Set.union (Ast.ClauseSet.pvs_of cls2)
      @@ Set.concat_map cls2 ~f:(fun (_, _, _, phi) ->
          Set.inter (Ast.Logic.Term.fvs_of phi) unknowns)
    in
    let blocked =
      (* the two conditions the refutation needs that [pvs2] does not give
         (see above): [P] in a pure part of a clause of the eliminated shape,
         and a clause of [P] whose pure part mentions an unknown *)
      Set.Poly.union_list
      @@ List.map (Set.to_list cls1) ~f:(fun ((_, _, _, phi) as cl) ->
          let in_phi = Set.inter (Ast.Logic.Term.fvs_of phi) unknowns in
          if Set.is_empty in_phi then in_phi
          else Set.union in_phi (Ast.Clause.pvs_of cl))
    in
    let cls11, cls12 =
      Set.partition_tf cls1 ~f:(fun cl ->
          let p = Set.choose_exn @@ Ast.Clause.pvs_of cl in
          (not @@ Set.mem pvs2 p) && not (Set.mem blocked p))
    in
    let clss, sol_eliminated =
      cls11
      |> Ast.ClauseSet.to_old_clause_set (PCSP.Problem.senv_of pcsp)
      |> Set.to_list
      |> List.classify (fun (_, _, ns1, _) (_, _, ns2, _) ->
          Ast.Ident.pvar_equal
            (Ast.LogicOld.Atom.pvar_of @@ Set.choose_exn ns1)
            (Ast.LogicOld.Atom.pvar_of @@ Set.choose_exn ns2))
      |> List.partition_map ~f:(function
        | [] -> assert false
        | (_, _, ns, _) :: _ as lst -> (
            let cls = Ast.ClauseSet.of_old_clause_set @@ Set.Poly.of_list lst in
            let open Ast in
            let open Ast.LogicOld in
            let pvar, sorts, _, _ = Atom.let_pvar_app @@ Set.choose_exn ns in
            let tvar = Ident.pvar_to_tvar pvar in
            let tot_positions =
              (* [None] for FN, which keeps its own solution shape below *)
              if PCSP.Problem.is_fn_pred pcsp tvar then None
              else (
                (* act counter: a [Tot] unknown is eliminated here only
                   under [eliminate_tot_preds] *)
                Common.PhaseTime.event "tot-elimination/attempt";
                Kind.tot_positions_of @@ PCSP.Problem.kind_of pcsp tvar)
            in
            let args = mk_fresh_sort_env_list sorts in
            let params = Term.of_sort_env args in
            let body =
              Formula.and_of
              @@ List.map lst ~f:(fun (uni_senv, _, ns, phi) ->
                  let uni_senv = Logic.to_old_sort_env_map uni_senv in
                  let _, _, ts, _ = Atom.let_pvar_app @@ Set.choose_exn ns in
                  let phi =
                    Formula.mk_forall_if_bounded (Map.Poly.to_alist uni_senv)
                    @@ Formula.mk_imply
                         (Formula.and_of @@ List.map2_exn ts params ~f:Formula.eq)
                         phi
                  in
                  (* the elimination is an equivalence, so where Z3's answer
                     cannot be read back -- it writes [seq.nth_u] for a read
                     out of range, which has no term here -- the formula is
                     kept as it is, which is what [qelim] returns when it
                     declines; any other failure still propagates *)
                  try Z3Smt.Z3interface.qelim ~id:None ~fenv:(get_fenv ()) phi
                  with
                  | Failure msg when UnreadableAnswer.is_failure msg ->
                    phi)
            in
            let univ, exis =
              match tot_positions with
              | None ->
                  let univ, ret = List.rest_last args in
                  (univ, [ ret ])
              | Some u ->
                  List.partition_map (List.mapi args ~f:(fun i x -> (i, x)))
                    ~f:(fun (i, x) ->
                      if List.mem u i ~equal:Int.equal then First x
                      else Second x)
            in
            let phi =
              Evaluator.simplify_neg @@ Formula.elim_ite
              @@ Formula.mk_forall_if_bounded univ
              @@ Formula.mk_exists_if_bounded exis
              @@ Formula.aconv_tvar body
            in
            let bool_result =
              match (tot_positions, exis) with
              | None, [ (r, s) ]
                when Term.is_bool_sort s && Formula.is_quantifier_free body ->
                  Some r
              | _ -> None
            in
            let term_result =
              (* quantifier elimination may decline (Z3 keeps the binder of
                 [forall y. y = x => phi] over bit-vectors), so where every
                 clause's atom has distinct variables as arguments and its
                 pure part mentions no other variable, the one-point rule
                 gives the same meaning quantifier-free *)
              let one_point () =
                Option.map ~f:Formula.and_of @@ Option.all
                @@ List.map lst ~f:(fun (_, _, ns, phi) ->
                    let _, _, ts, _ = Atom.let_pvar_app @@ Set.choose_exn ns in
                    match
                      Option.all
                      @@ List.map ts ~f:(function
                        | Term.Var (x, _, _) -> Some x
                        | _ -> None)
                    with
                    | Some xs
                      when (not (List.contains_dup ~compare:Stdlib.compare xs))
                           && Set.is_subset (Formula.tvs_of phi)
                                ~of_:(Set.Poly.of_list xs)
                           && Formula.is_quantifier_free phi ->
                        Some
                          (Formula.subst
                             (Map.Poly.of_alist_exn
                             @@ List.map2_exn xs args ~f:(fun x (y, s) ->
                                 (x, Term.mk_var y s)))
                             phi)
                    | _ -> None)
              in
              match (tot_positions, exis) with
              | None, [ (r, s) ]
                when Term.is_dt_sort s || Term.is_array_sort s
                     || Term.is_bv_sort s ->
                  if Formula.is_quantifier_free body then Some (r, s, body)
                  else Option.map (one_point ()) ~f:(fun b -> (r, s, b))
              | _ -> None
            in
            match (bool_result, term_result) with
            | Some r, _ -> eliminate_bool_fn_pred ~cls ~tvar ~args ~univ ~r body
            | None, Some (r, sort, body) ->
                (* the game's readers take neither sort, so nothing else is
                   tried when this keeps the clauses *)
                eliminate_term_fn_pred ~cls ~lst ~tvar ~args ~univ ~r ~sort
                  body
            | None, None -> (
            let open StratSynth in
            let game =
              let t = Logic.ExtTerm.of_old_formula phi in
              match LIA.formula_of_term t with
              | Some phi ->
                  Some
                    (witnesses_of_game
                       ~nondet:LIAStrategySynthesis.nondet_strategy_synthesis
                       ~is_sat:(function
                         | LIAStrategySynthesis.SAT -> true | _ -> false)
                       ~neg_formula:(PreFormula.neg_formula LIA.neg_atom)
                       ~lose:LIAStrategySynthesis.loseCHC phi)
              | None -> (
                  match LRA.formula_of_term t with
                  | None -> None
                  | Some phi ->
                      Some
                        (witnesses_of_game
                           ~nondet:LRAStrategySynthesis.nondet_strategy_synthesis
                           ~is_sat:(function
                             | LRAStrategySynthesis.SAT -> true | _ -> false)
                           ~neg_formula:(PreFormula.neg_formula LRA.neg_atom)
                           ~lose:LRAStrategySynthesis.loseCHC phi))
            in
            match (game, tot_positions) with
            | (None | Some `Undecided), _ -> First cls
            | Some `Refuted, None ->
                raise
                  (NoSolution
                     "strategy synthesis: an FN predicate cannot be total")
            | Some `Refuted, Some _ ->
                raise
                  (NoSolution
                     "strategy synthesis: a Tot predicate occurring only \
                      negatively cannot be total")
            | Some (`Witnesses sub), None ->
                let ret = List.hd_exn exis in
                let tret = Logic.Term.mk_var @@ fst ret in
                let senv, t = Map.Poly.find_exn sub @@ fst ret in
                Second
                  ( tvar,
                    Logic.Term.mk_lambda
                      (Map.to_alist senv
                      @ [ (fst ret, Logic.ExtTerm.of_old_sort @@ snd ret) ])
                    @@ Logic.BoolTerm.eq_of
                         (Logic.ExtTerm.of_old_sort @@ snd ret)
                         tret t )
            | Some (`Witnesses sub), Some _ ->
                (* the graph of the witness function, over [P]'s parameters in
                   their own order; an existential with no strategy does not
                   occur in [body] and is left unconstrained, which keeps the
                   relation total and inside [body] *)
                Second
                  ( tvar,
                    Logic.Term.mk_lambda
                      (List.map args ~f:(fun (x, s) ->
                           (x, Logic.ExtTerm.of_old_sort s)))
                    @@ Logic.BoolTerm.and_of
                    @@ List.filter_map exis ~f:(fun (x, s) ->
                        Option.map (Map.Poly.find sub x) ~f:(fun (_, t) ->
                            Logic.BoolTerm.eq_of
                              (Logic.ExtTerm.of_old_sort s)
                              (Logic.Term.mk_var x) t)) ))))
    in
    let pvs1 = Set.Poly.of_list @@ List.map ~f:fst sol_eliminated in
    let params = PCSP.Problem.params_of pcsp in
    (* [clauses] above is the full clause set, the stable clauses included,
       and the problem below is rebuilt from [params], whose stable clauses
       [PCSP.Problem.clauses_of] adds back.  A stable clause of an eliminated
       predicate is solved by its strategy like any other of its clauses, so
       it is dropped here with them: kept, it brought back an application of
       a predicate no longer in [senv], and the first reader of the problem
       that looks a predicate up in [senv] (the qualifier generator's
       normalisation) stopped with [Not_found_s].  Postcondition: no clause
       of the result applies a predicate of [pvs1]. *)
    let params =
      {
        params with
        senv = Map.Poly.filter_keys params.senv ~f:(Set.mem pvs1 >> not);
        kind_map = Map.Poly.filter_keys params.kind_map ~f:(Set.mem pvs1 >> not);
        stable_clauses =
          Set.filter params.stable_clauses ~f:(fun cl ->
              Set.is_empty (Set.inter (Ast.Clause.pvs_of cl) pvs1));
      }
    in
    ( Map.Poly.of_alist_exn sol_eliminated,
      PCSP.Problem.of_clauses ~params
        (Set.Poly.union_list (cls12 :: cls2 :: clss)) )

  (* An unknown this synthesizer has no template for is an unsupported INPUT,
     and the answer to one of those is [unknown] -- an ordinary verdict here.
     Letting it out as an exception makes it a backtrace for the user and a
     crash for a corpus sweep, which records a crash in the cell a timeout gets
     and so hides it; three shipped benchmarks ended that way. *)
  let rec solve ?(witness = WitnessConfig.default) ?(oracle = None) pcsp =
    try
      match prove_unknown_free_first ~witness ~oracle pcsp with
      | `Decided result -> result
      | `Rest pcsp -> solve_aux ~witness ~oracle pcsp
    with PCSP.Problem.NoTemplate reason ->
      (* on the diagnostic stream unconditionally, as the sibling handler at the
         dispatcher does: [unknown] with no reason is the least useful answer
         this tool can give, and a reason behind a tracing flag is one the
         person who met the refusal does not have *)
      prerr_endline ("unsupported input: " ^ reason);
      Ok
        ( PCSP.Problem.Unknown,
          {
            State.num_cegis_iters = 0;
            unsat_witness = None;
            kind_certificates = Map.Poly.empty;
          } )

  (* [unknown_free_clauses.prove_first].  Contract: [`Rest p] is either [pcsp]
     itself or [pcsp] without clauses that mention no unknown and that the
     zero-unknown verdict answered [sat] for, i.e. proved valid in every model
     of the theory; such a clause holds under every interpretation of the
     unknowns, so [p] and [pcsp] have the same solutions and a solution of [p]
     is one of [pcsp].  [`Decided r] is only an [unsat] of those clauses
     alone: they hold under no interpretation, so neither does [pcsp].  Why
     it exists: a loop that keeps such a clause asks it again in every
     validation round with a plain solver query, and a clause over a generic
     iterator's relations (sorts left open, sequences under quantifiers)
     that only the zero-unknown verdict's instantiations decide is then
     never proved, so no candidate is ever accepted however right it is. *)
  and prove_unknown_free_first ~witness ~oracle pcsp =
    let senv = PCSP.Problem.senv_of pcsp in
    match config.unknown_free_clauses.prove_first with
    | No_prove_first -> `Rest pcsp
    | Prove_first pf ->
    if Map.Poly.is_empty senv then `Rest pcsp
    else
      match PCSP.Problem.clauses_of_opt ~full_clauses:false pcsp with
      | None -> `Rest pcsp
      | Some cnf -> (
          let params = PCSP.Problem.params_of pcsp in
          let is_free = UnknownFreeSweep.unknown_free senv in
          let free =
            Set.filter (PCSP.Problem.clauses_of pcsp) ~f:is_free
          in
          (* [beyond_arithmetic]: whether
             some variable of [free], free or bound, has a sort other than
             an arithmetic or Boolean one *)
          let beyond_arithmetic () =
            let open Ast.LogicOld in
            let arith = function
              | T_int.SInt | T_real.SReal | T_bool.SBool | T_bv.SBV _ -> true
              | _ -> false
            in
            Set.exists
              (Ast.ClauseSet.to_old_clause_set Map.Poly.empty free)
              ~f:(fun c ->
                let phi = Ast.ClauseOld.to_formula c |> snd in
                Set.exists (Formula.term_sort_env_of phi) ~f:(fun (_, s) ->
                    not (arith s))
                || Set.exists (Formula.quantified_sort_env_of phi)
                     ~f:(fun (_, s) -> not (arith s)))
          in
          if Set.is_empty free then `Rest pcsp
          else if
            pf.beyond_arithmetic
            && not (beyond_arithmetic ())
          then (
            Debug.print
            @@ lazy
                 (sprintf
                    "[unknown-free first] not run: the %d clause(s) without \
                     an unknown are over arithmetic alone"
                    (Set.length free));
            `Rest pcsp)
          else
            let started = Common.Clock.now_s () in
            let sub =
              PCSP.Problem.of_clauses
                ~params:
                  {
                    params with
                    senv = Map.Poly.empty;
                    stable_clauses = Set.Poly.empty;
                  }
                free
            in
            let in_process () =
              Common.PhaseTime.with_phase "unknown-free-first" (fun () ->
                  solve_aux ~witness ~oracle sub)
            in
            let no_cert_unsat =
              Ok
                ( PCSP.Problem.Unsat None,
                  {
                    State.num_cegis_iters = 0;
                    unsat_witness = None;
                    kind_certificates = Map.Poly.empty;
                  } )
            in
            let result =
              let budget_ms =
                match pf.budget_ms with
                | Some ms when pf.within_deadline
                  -> (
                    match PCSatCommon.SolveDeadline.remaining_ms () with
                    | Some r -> Some (Int.min ms r)
                    | None -> Some ms)
                | b -> b
              in
              match budget_ms with
              | None -> in_process ()
              | Some _
                when pf.within_deadline
                     && PCSatCommon.SolveDeadline.expired () ->
                  Ok
                    ( PCSP.Problem.Unknown,
                      {
                        State.num_cegis_iters = 0;
                        unsat_witness = None;
                        kind_certificates = Map.Poly.empty;
                      } )
              | Some ms
                when not
                       (Common.ForkGuard.fits
                          ~growth:(Common.ForkGuard.peak_excess_bytes ())
                          ())
                ->
                  (* too large to copy: in this process, under the same
                     budget, as a strict deadline.  The copy would solve the
                     unknown-free clauses again from this process's heap, so
                     its need is the whole heap (its collector writes every
                     live page) plus the process's own peak excess, beside
                     the copies already alive; a copy past that is what the
                     memory cap kills, with the whole run.  Taken whatever
                     [in_process_when_large]
                     says: the field asked for this test alone, which the
                     shared budget now always applies *)
                  Atomic.incr Common.ForkGuard.refused;
                  Common.PhaseTime.event_here "fork-refused/memory";
                  Common.PhaseTime.with_phase "unknown-free-first-large"
                    (fun () ->
                      try
                        PCSatCommon.SolveDeadline.within ~strict_budget:true
                          ~seconds:(Float.of_int ms /. 1000.)
                          (fun () -> solve_aux ~witness ~oracle sub)
                      with exn_ when not (Common.Timer.is_async exn_) ->
                        Or_error.of_exn exn_)
              | Some ms -> (
                  (* only a plain tag comes back from the copy: a solution or
                     a certificate holds extensible variants, which do not
                     survive marshalling *)
                  match
                    Common.PhaseTime.with_phase "unknown-free-first-forked"
                      (fun () ->
                        PCSatCommon.ForkedQuery.run
                          ~growth:(Common.ForkGuard.peak_excess_bytes ())
                          ~ms (fun () ->
                            match solve_aux ~witness ~oracle sub with
                            | Ok (PCSP.Problem.Sat _, _) -> `Valid
                            | Ok (PCSP.Problem.Unsat _, _) -> `Refuted
                            | _ -> `Undecided))
                  with
                  | Some `Valid -> Ok (PCSP.Problem.Sat Map.Poly.empty, {
                        State.num_cegis_iters = 0;
                        unsat_witness = None;
                        kind_certificates = Map.Poly.empty;
                      })
                  | Some `Refuted ->
                      if WitnessConfig.records_unsat witness then (
                        (* the certificate is built here; should this run
                           not refute again, the pass decides nothing *)
                        match in_process () with
                        | Ok (PCSP.Problem.Unsat _, _) as r -> r
                        | _ -> Ok (PCSP.Problem.Unknown, {
                              State.num_cegis_iters = 0;
                              unsat_witness = None;
                              kind_certificates = Map.Poly.empty;
                            }))
                      else no_cert_unsat
                  | Some `Undecided | None ->
                      Ok (PCSP.Problem.Unknown, {
                          State.num_cegis_iters = 0;
                          unsat_witness = None;
                          kind_certificates = Map.Poly.empty;
                        }))
            in
            let verdict =
              match result with
              | Ok (PCSP.Problem.Sat _, _) -> "valid"
              | Ok (PCSP.Problem.Unsat _, _) -> "refuted"
              | Ok _ -> "undecided"
              | Error _ -> "error"
            in
            Debug.print
            @@ lazy
                 (sprintf
                    "[unknown-free first] %d clause(s) without an unknown \
                     (of %d), %d unknown(s): %s in %.2f s"
                    (Set.length free)
                    (Set.length (PCSP.Problem.clauses_of pcsp))
                    (Map.Poly.length senv) verdict
                    (Common.Clock.now_s () -. started));
            match result with
            | Ok (PCSP.Problem.Sat _, _) ->
                `Rest
                  (PCSP.Problem.of_clauses
                     ~params:
                       {
                         params with
                         stable_clauses =
                           Set.filter params.stable_clauses
                             ~f:(is_free >> not);
                       }
                     (Set.filter cnf ~f:(is_free >> not)))
            | Ok (PCSP.Problem.Unsat _, _) -> `Decided result
            | _ -> `Rest pcsp)

  and solve_aux ~witness ~oracle pcsp =
    let senv = PCSP.Problem.senv_of pcsp in
    let if_witness w = if WitnessConfig.records_unsat witness then Some w else None in
    match
      Set.find
        (PCSP.Problem.formulas_of pcsp)
        ~f:(snd >> Ast.Logic.BoolTerm.is_false)
    with
    | Some (uni_senv, term) ->
        let unsat_witness =
          if_witness
            (UnsatWitness.make ~problem:(Some pcsp) senv
               (UnsatWitness.FalseConstraint (uni_senv, term)))
        in
        Ok
          ( PCSP.Problem.Unsat (Option.map unsat_witness ~f:payload_of),
            {
              State.num_cegis_iters = 0;
              unsat_witness;
              kind_certificates = Map.Poly.empty;
            } )
    | None -> (
        if Map.Poly.is_empty senv then
          Common.PhaseTime.with_phase "zero-unknown" @@ fun () ->
          (fun body ->
            if not config.zero_unknown.budgets.reads_strict_deadline then body ()
            else
              try body ()
              with Zero_unknown_deadline_passed ->
                Debug.print
                @@ lazy
                     "[no-unknown verdict] the strict solve deadline has \
                      passed; unknown";
                Ok
                  ( PCSP.Problem.Unknown,
                    {
                      State.num_cegis_iters = 0;
                      unsat_witness = None;
                      kind_certificates = Map.Poly.empty;
                    } ))
          @@ fun () ->
          Z3Smt.Z3interface.with_arith_solver
            config.zero_unknown.budgets.arith_solver
          @@ fun () ->
          let rewrites = ladder_question_rewrites config in
          PCSatCommon.ValidityAsk.with_int_binder_split rewrites
          @@ fun () ->
          (* [zero_unknown.rewrites.rejoin_single_cons_fields]: every stage
             below reads the clauses of [pcsp] (the conjunction, the pieces,
             the point and relation pins), so the fold is applied here, once,
             to the problem itself; the problem is untouched when nothing is
             folded, but the attempt is not free of effects: every clause makes
             a round trip through the old term representation and a clause
             with a candidate group is alpha-converted, and both draw names
             from the process-global fresh-name counter.  So with nothing
             folded, every name drawn after this point still differs from the
             run with the field off, and so may the path of every later stage
             that names a variable.  The event says which of the two happened:
             [rejoin-single-cons-fields] when a group was folded,
             [rejoin-single-cons-fields-none] when the fold ran and folded
             nothing *)
          let pcsp =
            if not config.zero_unknown.rewrites.rejoin_single_cons_fields then
              pcsp
            else
              let count_before = Atomic.get Ast.Ident.tvar_count in
              let folded = ref 0 in
              let pcsp' =
                PCSP.Problem.map_old pcsp ~f:(fun (uni_senv, phi) ->
                    let uni_senv, phi, n =
                      Ast.Evaluator.rejoin_single_cons_fields_in uni_senv phi
                    in
                    folded := !folded + n;
                    (uni_senv, phi))
              in
              (* other domains draw from the same counter, so this is an
                 upper bound on the names the fold drew; 0 inside a replay *)
              let drawn = Atomic.get Ast.Ident.tvar_count - count_before in
              if !folded = 0 then (
                Common.PhaseTime.event_here "rejoin-single-cons-fields-none";
                Debug.print
                @@ lazy
                     (sprintf
                        "[no-unknown verdict] single-constructor field groups \
                         folded back: none (fresh names drawn meanwhile: %d)"
                        drawn);
                pcsp)
              else (
                Common.PhaseTime.event_here "rejoin-single-cons-fields";
                Debug.print
                @@ lazy
                     (sprintf
                        "[no-unknown verdict] single-constructor field groups \
                         folded back: %d (fresh names drawn meanwhile: %d)"
                        !folded drawn);
                pcsp')
          in
          let phi =
            Ast.ClauseSetOld.to_formula
            @@ Ast.ClauseSet.to_old_clause_set Map.Poly.empty
            @@ PCSP.Problem.clauses_of pcsp
          in
          let iters =
            {
              State.num_cegis_iters = 0;
              unsat_witness = None;
              kind_certificates = Map.Poly.empty;
            }
          in
          (* No predicate variable is left, so the problem is satisfiable
             exactly when the remaining constraints hold whatever the
             background theory left open -- a selector on the wrong
             constructor ([tl nil]), an uninterpreted function, a division by
             zero.  That is validity and not satisfiability: the constraints
             are the obligation an implementation must meet, and an
             implementation is committed only to the theory, so a formula
             that some model of the theory falsifies is not one it may rely
             on.  Z3's unknown/timeout must not become a definite verdict. *)
          (* Open an existential over a SINGLE-constructor datatype into one over
             its fields.  Every value of such a sort is that constructor applied to
             some fields and the fields are determined, so
               exists (p : D). phi   <=>   exists (f1 .. fk). phi[p := C f1 .. fk]
             holds in both directions -- the same fact that makes a selector of a
             single-constructor datatype total, which the interpretation-dependence
             classifier already relies on.  Why it is worth asking twice: Z3
             instantiates a quantifier with ground terms the query already holds,
             and a query that never builds a value of the pair sort gives it
             nothing to instantiate with -- it answers "unknown (incomplete (theory
             array))" -- while the same question over the fields is decided at
             once, because the fields ARE in the query.  Only the binder is
             rewritten; nothing under a binder is opened recursively, so a
             single-constructor recursive datatype is opened one level. *)
          let rec open_single_cons_binders phi =
            let open Ast.LogicOld in
            match phi with
            | Formula.Bind (binder, bound, body, info) ->
                let body = open_single_cons_binders body in
                let bound', sub =
                  List.fold_right bound ~init:([], Map.Poly.empty)
                    ~f:(fun (x, sort) (acc, sub) ->
                      match sort with
                      | T_dt.SDT dt
                        when List.length (Datatype.conses_of dt) = 1 ->
                          let cons = List.hd_exn (Datatype.conses_of dt) in
                          let fields =
                            List.map (Datatype.sorts_of_cons dt cons) ~f:(fun s ->
                                (Ast.Ident.mk_fresh_tvar (), s))
                          in
                          let t =
                            T_dt.mk_cons dt (Datatype.name_of_cons cons)
                            @@ List.map fields ~f:(fun (f, s) -> Term.mk_var f s)
                          in
                          (fields @ acc, Map.Poly.add_exn sub ~key:x ~data:t)
                      | _ -> ((x, sort) :: acc, sub))
                in
                let body =
                  if Map.Poly.is_empty sub then body else Formula.subst sub body
                in
                Formula.mk_bind ~info binder bound' body
            | Formula.UnaryOp (op, p, _) ->
                Formula.mk_unop op (open_single_cons_binders p)
            | Formula.BinaryOp (op, p1, p2, _) ->
                Formula.mk_binop op (open_single_cons_binders p1)
                  (open_single_cons_binders p2)
            | phi -> phi
          in
          (* Each clause is put in the form a solver decides best before it
             is asked, by two rewrites that are EXACT -- each clause is
             equivalent to its rewritten form in every model -- so the verdict
             is the same question: a sequence variable a clause defines as a
             concatenation, unit or empty sequence is substituted by its
             definition, and every read of a concatenation is split by index.
             Only clauses that read a sequence are touched.  A read of a
             concatenation under a quantified hypothesis about the parts was
             observed to leave the whole conjunction undecided, and this query
             carried no budget, so the process hung here although the problem
             had no predicate variable left. *)
          (* the witness check of [eliminate_guarded_length_only_sequences]:
             a quantifier-free linear question over a guard's body, read only
             when proved; asked under a resource limit, with no wall clock *)
          let guard_witness_valid phi =
            match
              Z3Smt.Z3interface.with_rlimit (Some 2_000_000) (fun () ->
                  Z3Smt.Z3interface.check_valid ~timeout:None ~id:None
                    (Ast.LogicOld.get_fenv ()) phi)
            with
            | `Valid -> true
            | _ -> false
          in
          let prepare phi =
            let phi =
              if config.zero_unknown.rewrites.guarded_length_only_sequences
              then
                Common.PhaseTime.with_phase "guarded-length-only" (fun () ->
                    Ast.Evaluator.eliminate_guarded_length_only_sequences
                      ~valid:guard_witness_valid phi)
              else phi
            in
            let phi =
              if config.zero_unknown.rewrites.subst_projection_definitions then
                Ast.Evaluator.subst_seq_projection_definitions phi
              else phi
            in
            (* the read split, then the prefix split where [rewrites] asks
               for it, untimed as before *)
            Ast.QuestionRewrites.formula_rewrites ~phases:false rewrites phi
          in
          let per_clause =
            List.map ~f:prepare @@ Set.to_list @@ Ast.ClauseSetOld.to_formulas
            @@ Ast.ClauseSet.to_old_clause_set Map.Poly.empty
            @@ PCSP.Problem.clauses_of pcsp
          in
          (* [COAR_DUMP_UNKNOWN_FREE_CLAUSES=dir] (instrument only): each clause
             the verdict is about to decide is written as [dir/cN-PID_native.smt2],
             its negation, before anything is asked; nothing is written and
             nothing changes without the variable. *)
          Option.iter (Sys.getenv "COAR_DUMP_UNKNOWN_FREE_CLAUSES")
            ~f:(fun dir ->
              let fenv = Ast.LogicOld.get_fenv () in
              List.iteri per_clause ~f:(fun i c ->
                  Z3Smt.Z3interface.with_query_dump
                    (sprintf "%s/c%d-%d" dir i (Common.ForkGuard.self_pid ()))
                    (fun () ->
                      Z3Smt.Z3interface.dump_native_question ~id:None fenv c)));
          let asked = Ast.LogicOld.Formula.and_of per_clause in
          (* The same clauses after the one-point rule, the single-constructor
             split and the sequence-length split, when switched on.  The
             rewrites are equivalences in every model and add no free
             variable, so a
             countermodel of a rewritten clause is one of the clause it came
             from, and the question stays the same one.  They are asked AFTER
             the unrewritten forms, so switching them on cannot lose an answer
             those decide; what they buy is a validity question over a pair
             that only a selector reads, or over a bound variable an equation
             defines, where the solver has no ground term to instantiate the
             quantifier with and answers "incomplete (theory array)". *)
          let contextual_in_place, contextual_extra =
            set_onepoint_rewrite_switches ()
          in
          let per_clause_rewritten =
            if config.zero_unknown.rewrites.onepoint.split then
              Some
                (List.map per_clause
                   ~f:Ast.Evaluator.elim_onepoint_and_split_binders)
            else None
          in
          (* Every query on this path carries a budget of ten seconds, and an
             undecided answer is carried out as [unknown] or [timeout], never
             as a verdict.  The value is a choice, not a measurement: it costs
             an answer only where a single validity query needs longer, and
             without a budget such a query stops the process instead.
             Unlike the preprocessing sites, a query here is NOT refused for
             its shape ([may_not_return]: a quantifier binding a sequence or a
             regular expression).  This is the last question a problem with no
             predicate variable left gets, so refusing it is refusing the
             answer, and it was measured to be one: a Rust-derived problem
             whose final constraint binds a sequence is decided valid by the
             solver within seconds, and the refusal turned its [sat] into
             [unknown].  Where the budget does not hold over such a binder the
             call behaves as it did with no budget at all. *)
          (* [~enabled] (default [true]) is how a fresh-context ask applies
             [zero_unknown.axioms.first.fresh]; see [AxiomsFirst.ask]
             for the order and why it changes only timing *)
          let axioms_first ?(enabled = true) phi k =
            match (ZeroUnknownConfig.Switch.seq_axioms_first config.zero_unknown) with
            | Some ms ->
                AxiomsFirst.ask ~enabled
                  ~applies:Ast.SeqAxiomEncoding.mentions_seq
                  ~prove:(fun phi ->
                    match
                      Z3Smt.Z3interface.prove_valid_by_seq_axioms ~timeout:ms
                        ~id:None (Ast.LogicOld.get_fenv ()) phi
                    with
                    | Z3Smt.Z3interface.SeqAxProved -> true
                    | _ -> false)
                  ~native:k phi
            | None -> k phi
          in
          (* how many questions below ran out of their budget, for the
             report at the end (see [zero_unknown.budgets.report_exhaustion]); every query
             goes through [budgeted], which also applies the rlimit *)
          let budget_cut = ref 0 in
          let budget_asked = ref 0 in
          (* [zero_unknown.axioms.first_after_fallback_proof]: armed once a
             fresh question of this verdict ran its native question to its
             budget and the sequence-axiom fallback then proved it; from
             then on the fresh questions ask the axiomatised form first, as
             [axioms.first.fresh] does.  Per verdict: a later verdict starts
             unarmed *)
          let after_fallback_proof =
            PCSatCommon.AxiomsFirst.After_fallback_proof.create
              ~on:
                (ZeroUnknownConfig.Switch.seq_axioms_first_after_fallback_proof
                   config.zero_unknown)
          in
          (* LADDER-PROFILE tracing: which stage of the ladder a question
             belongs to, printed with each question and at each transition *)
          let ladder_phase = ref "start" in
          let ladder_t0 = Common.Clock.now_s () in
          let ladder_stage, _ = Common.PhaseTime.stages () in
          let deadline_passed () =
            config.zero_unknown.budgets.reads_strict_deadline
            && PCSatCommon.SolveDeadline.expired_strict ()
          in
          let enter_phase name =
            if deadline_passed () then (
              PCSatCommon.SolveDeadline.cut ();
              raise Zero_unknown_deadline_passed);
            ladder_stage name;
            ladder_phase := name;
            Debug.print
            @@ lazy
                 (sprintf "[no-unknown verdict] phase %s at %.2f s" name
                    (Common.Clock.now_s () -. ladder_t0))
          in
          let stage_rlimit =
            LadderStageRlimit.find
              ~stage_rlimits:config.zero_unknown.budgets.stage_rlimits
              ~default:config.zero_unknown.budgets.query_rlimit
          in
          let budgeted f =
            let started = Common.Clock.now_s () in
            let r =
              (* past a strict deadline the question is not asked; it is
                 reported as one that ran out of its budget, which every
                 caller reads as undecided *)
              if deadline_passed () then (
                PCSatCommon.SolveDeadline.cut ();
                `Timeout)
              else
                (* with [zero_unknown.axioms.ladder_fallback], the
                   fallback is asked under its count and its own budget (Z3
                   parameters, a kill only in a forked copy); the lemma route
                   sets its own pair inside; with
                   either refinement of the pair, it is chosen per fresh
                   question in [fresh_body] instead *)
                (* with [zero_unknown.axioms.fork_fallbacks], every
                   fallback check inside is asked in a killed copy, the one
                   bound on it that holds *)
                Z3Smt.Z3interface.with_seq_axiom_fork_runner
                  (if config.zero_unknown.axioms.fork_fallbacks then
                     Some
                       (fun ~ms ask ->
                         let r = PCSatCommon.ForkedQuery.run_forked ~ms ask in
                         (* counted only: a fallback check asked in a copy
                            (`Not_forked asks it in process, as without the
                            field); [r] is returned either way *)
                         Common.PhaseTime.event_here
                           (match r with
                           | `Value _ -> "fallback-fork/value"
                           | `Lost -> "fallback-fork/lost"
                           | `Not_forked -> "fallback-fork/not-forked");
                         r)
                   else None)
                @@ fun () ->
                LadderSeqAxiomRlimit.with_
                  (LadderSeqAxiomRlimit.around_question
                     ~refused_only:
                       (ZeroUnknownConfig.Switch.ladder_seq_axiom_rlimit_refused_only config.zero_unknown)
                     ~per_node:(ZeroUnknownConfig.Switch.ladder_seq_axiom_units_per_node config.zero_unknown)
                     (ZeroUnknownConfig.Switch.ladder_seq_axiom_rlimit config.zero_unknown))
                @@ fun () ->
                Z3Smt.Z3interface.with_rlimit
                  ~label:(sprintf "q%d:%s" !budget_asked !ladder_phase)
                  (stage_rlimit !ladder_phase) f
            in
            Z3Smt.Z3interface.rlimit_log_line_lazy
            @@ lazy
                 (sprintf "QUESTION\t%d\tq%d:%s\t%s\t%.3f"
                    (Core_unix.getpid () |> Pid.to_int)
                    !budget_asked !ladder_phase
                    (match r with
                    | `Valid -> "valid"
                    | `Invalid _ -> "invalid"
                    | `Timeout -> "timeout"
                    | `Unknown reason ->
                        "unknown:"
                        ^ String.tr ~target:'\t' ~replacement:' ' reason
                    | `Sat _ | `Unsat -> "unexpected")
                    (Common.Clock.now_s () -. started));
            Debug.print
            @@ lazy
                 (sprintf "[no-unknown verdict] question %d [%s]: %s in %.2f s"
                    !budget_asked !ladder_phase
                    (match r with
                    | `Valid -> "valid"
                    | `Invalid _ -> "invalid"
                    | `Timeout -> "timeout"
                    | `Unknown reason -> "unknown: " ^ reason
                    | `Sat _ | `Unsat -> "unexpected")
                    (Common.Clock.now_s () -. started));
            incr budget_asked;
            (match r with `Timeout -> incr budget_cut | _ -> ());
            r
          in
          (* printed BEFORE a question is asked, so that a question that
             does not return is named by the last line of a trace: the
             answer line [budgeted] prints comes only after the call *)
          let note_asking ~kind timeout phi =
            Debug.print
            @@ lazy
                 (sprintf
                    "[no-unknown verdict] asking question %d [%s] (%s): size \
                     %d, budget %d ms, at %.2f s"
                    !budget_asked !ladder_phase kind
                    (Ast.LogicOld.Formula.ast_size phi)
                    timeout
                    (Common.Clock.now_s () -. ladder_t0))
          in
          (* [zero_unknown.pins.pointwise_array_countermodels]: an undecided
             [answer] to the validity question [phi] is followed by the
             question about its instance at the pointwise definitions of its
             free arrays ([SeqInstantiation.pointwise_array_instance]), of
             which only a model of the negation is read: a countermodel of an
             instance is one of [phi], the arrays taking the lambdas' values,
             which are added to the model.  A decided [answer] is returned as
             it is, as is everything when the switch is off or no free array
             has a definition. *)
          let pointwise_refute ~timeout phi answer =
            match answer with
            | `Valid | `Invalid _ -> answer
            | _ when not config.zero_unknown.pins.pointwise_array_countermodels
              ->
                answer
            | _ -> (
                match SeqInstantiation.pointwise_array_instance phi with
                | None ->
                    Debug.print
                    @@ lazy
                         (sprintf
                            "[no-unknown verdict] pointwise array instance: \
                             none (free: %s)"
                            (String.concat ~sep:", "
                            @@ List.map
                                 (Set.to_list
                                    (Ast.LogicOld.Formula.term_sort_env_of phi))
                                 ~f:(fun (x, s) ->
                                   Ast.Ident.name_of_tvar x ^ ":"
                                   ^ Ast.LogicOld.Term.str_of_sort s)));
                    answer
                | Some (inst, defs) -> (
                    let open Ast.LogicOld in
                    let neg = Formula.nnf_of (Formula.negate inst) in
                    if Z3Smt.Z3interface.may_not_return neg then answer
                    else
                      (* an instance the solver rejects (an ill-sorted
                         substitution, which the reader of the definitions
                         should have refused) leaves the answer as it was:
                         only a countermodel is read from this question *)
                      let r =
                        try
                          Z3Smt.Z3interface.check_sat ~timeout:(Some timeout)
                            ~fresh_solver:true ~id:None
                            (Z3Smt.Z3interface.fenv_reached_by (get_fenv ())
                               neg)
                            [ neg ]
                        with Z3.Error msg ->
                          `Unknown ("rejected by the solver: " ^ msg)
                      in
                      Debug.print
                      @@ lazy
                           (sprintf
                              "[no-unknown verdict] pointwise array instance \
                               (%s): %s"
                              (String.concat ~sep:", "
                              @@ List.map defs ~f:(fun ((x, _), t) ->
                                  Ast.Ident.name_of_tvar x ^ " := "
                                  ^ Term.str_of t))
                              (match r with
                              | `Sat _ -> "a countermodel"
                              | `Unsat -> "none (says nothing)"
                              | `Timeout -> "timeout"
                              | `Unknown reason -> "unknown: " ^ reason));
                      match r with
                      | `Sat model ->
                          `Invalid
                            (model
                            @ List.map defs ~f:(fun (xs, t) -> (xs, Some t)))
                      | _ -> answer))
          in
          (* [~fresh:true] asks the same question in a Z3 context made for
             it and told only the defined functions it reaches (as the
             rewritten questions are asked, see below), instead of the pooled
             context; only [zero_unknown.external.conj_seq_binder] passes
             it *)
          let ask_within ?(fresh = false) timeout phi =
            note_asking ~kind:(if fresh then "fresh" else "pooled") timeout phi;
            budgeted @@ fun () ->
            pointwise_refute ~timeout phi
            @@ axioms_first phi @@ fun phi ->
            (if config.zero_unknown.rewrites.seq_as_array then
               Z3Smt.Z3interface.check_valid_seq_as_array
             else Z3Smt.Z3interface.check_valid)
              ~timeout:(Some timeout)
              ~fresh_solver:fresh ~id:None
              (if fresh then
                 Z3Smt.Z3interface.fenv_reached_by (Ast.LogicOld.get_fenv ())
                   phi
               else Ast.LogicOld.get_fenv ())
              phi
          in
          let ask = ask_within config.zero_unknown.budgets.query_ms in
          (* [conj_within timeout phi] asks the pooled whole-conjunction
             questions ([conj], [conj-opened]) as [ask_within] does, except
             that a question whose shape [may_not_return] refuses (a
             quantifier binding a sequence or a regular expression) is asked
             as [zero_unknown.external.conj_seq_binder] says: in process
             ([Asked_in_process], as before), in process in a fresh context
             ([Asked_fresh]), not at all ([Refused], answered [`Unknown]), or
             in a forked copy given the question's budget plus a margin
             ([Killed_copy], in the pooled or a fresh context).
             Contract: the result is [`Valid] or [`Invalid m] only when the
             very question [ask_within timeout phi] asks (the same formula,
             in the pooled or in a fresh context), asked in this process or
             in a copy of it forked at this point, answered so -- in the copy's case the copy has
             become the run and this call returns there; every other result
             is one the ladder reads as undecided, as it reads every such
             answer of these questions ([NoUnknownLadder.ask_conj]).  So each
             arm changes only how long an undecided question may take, and
             which questions are asked at all, never how an answer is read:
             [Refused] can lose a decision, [Killed_copy] only one reached
             after the kill.
             Why: asked in process, Z3's sequence theory does not read its
             cancel flag, and these questions returned after 20-36 s against
             a 10 s budget on a Rust-derived loop step, with every stack
             sample past the budget inside the sequence theory.
             With the phase account on, every question of the refused shape
             is counted as [conj-seqbinder:<outcome>], whatever the arm
             ([valid], [invalid] and [undecided] when asked in process,
             [refused], [killed] when the copy gave nothing back in time,
             [copy-undecided] when it answered neither, [in-copy] when it
             decided, counted in the copy that becomes the
             run), so a run under the default shows how often such a question
             decides; the count decides nothing. *)
          let conj_within timeout phi =
            if not (Z3Smt.Z3interface.may_not_return phi) then
              ask_within timeout phi
            else
              let counted r =
                Common.PhaseTime.event_here
                  ("conj-seqbinder:"
                  ^
                  match r with
                  | `Valid -> "valid"
                  | `Invalid _ -> "invalid"
                  | _ -> "undecided");
                r
              in
              match config.zero_unknown.external_.conj_seq_binder with
              | ZeroUnknownConfig.Asked_in_process -> counted (ask_within timeout phi)
              | ZeroUnknownConfig.Asked_fresh ->
                  counted (ask_within ~fresh:true timeout phi)
              | ZeroUnknownConfig.Refused ->
                  Common.PhaseTime.event_here "conj-seqbinder:refused";
                  `Unknown "not asked: the solver may not return on this shape"
              | ZeroUnknownConfig.Killed_copy { margin_ms; fresh } -> (
                  (* a nested solve under a cooperative deadline is not
                     handed to a copy, as the raced early pins are not *)
                  if PCSatCommon.SolveDeadline.active () then
                    counted (ask_within ~fresh timeout phi)
                  else
                    match
                      PCSatCommon.ParallelRace.decide_in_copy
                        ~ms:(timeout + Int.max margin_ms 0)
                        ~decisive:(function
                          | `Valid | `Invalid _ -> true | _ -> false)
                        (fun () -> ask_within ~fresh timeout phi)
                    with
                    | `Decided r ->
                        Common.PhaseTime.event_here "conj-seqbinder:in-copy";
                        r
                    | `Not_started -> counted (ask_within ~fresh timeout phi)
                    | `Undecided `Answered ->
                        (* the copy's answer was neither [`Valid] nor
                           [`Invalid _]; which undecided answer it was does
                           not come back, and every one reads the same *)
                        Common.PhaseTime.event_here
                          "conj-seqbinder:copy-undecided";
                        `Unknown "undecided in a forked copy"
                    | `Undecided `Killed ->
                        Common.PhaseTime.event_here "conj-seqbinder:killed";
                        (* counted as a question that ran out of its budget,
                           as [budgeted] counts one asked here *)
                        incr budget_asked;
                        incr budget_cut;
                        `Timeout)
          in
          (* The rewritten clauses are asked in a Z3 context made for the
             query and told only the defined functions they mention.  Both
             matter, and for the same reason: the goals the rewrite produces
             were measured to be decided by Z3's default preprocessing (the
             elimination of unconstrained terms) and left "incomplete
             quantifiers" by the bare [smt] tactic, and Z3 falls back to that
             tactic when the context holds any recursive function definition --
             every definition is registered as one, used or not -- and in a
             pooled context that has been in a scope before.  Leaving out a
             definition the goal does not reach, directly or through another
             definition, does not change what the goal means. *)
          let fenv_used_by phi =
            Z3Smt.Z3interface.fenv_reached_by (Ast.LogicOld.get_fenv ()) phi
          in
          (* The negation is put in negation normal form before it is asked,
             which the pooled path does as a side effect of expanding defined
             functions whenever there are any, and which an empty function
             environment skips: Z3 was measured to decide such a goal written
             with its quantifiers pushed inward ([forall] over the negated
             body) and to leave the same goal written [not (exists ...)]
             undecided. *)
          (* Unlike the unrewritten questions, these ARE refused for a shape
             the solver may not return on (a quantifier binding a sequence or a
             regular expression, where no budget holds): they are asked only
             after the unrewritten questions have failed, so refusing one costs
             nothing those decide, while asking one can stop the process before
             the last-resort refutation below is tried. *)
          (* An undecided answer here, a refusal included, is given to the
             sequence-axiom fallback when it is on ([check_valid], which
             [ask] uses, does the same by itself): it can only turn the answer
             into [`Valid], and only by proving the clause. *)
          (* [zero_unknown.rewrites.implied_factor_equalities]: the question with
             the factor equations its linear facts imply stated, an
             equivalence ([Z3interface.implied_factor_equalities]); [phi]
             itself when off *)
          let factor_eqs ~timeout phi =
            PCSatCommon.ValidityAsk.factor_equalities rewrites ~timeout
              ~id:None (Ast.LogicOld.get_fenv ()) phi
          in
          (* [native] asks the solver itself ([native_check] in-process, or a
             forked copy of it) *)
          (* [factor_ms]: the budget of [factor_eqs]'s questions, by default
             the question's own (10 s without one); a forked copy that asks
             with no Z3 timer passes the budget the in-process call would
             have given them *)
          let native_check ?factor_ms ~timeout phi =
            let open Ast.LogicOld in
            let phi =
              factor_eqs
                ~timeout:
                  (match factor_ms with
                  | Some ms -> ms
                  | None -> Option.value timeout ~default:10000)
                phi
            in
            match
              (if config.zero_unknown.rewrites.seq_as_array then
                 Z3Smt.Z3interface.check_sat_seq_as_array
               else Z3Smt.Z3interface.check_sat)
                ~timeout ~fresh_solver:true ~id:None (fenv_used_by phi)
                [ Formula.nnf_of (Formula.negate phi) ]
            with
            | `Unsat -> `Valid
            | `Sat model -> `Invalid model
            | res -> res
          in
          (* [native_check] in a forked copy killed after [ms], asked there
             with no Z3 timer (the thread serving it does not exist in a
             forked process), the kill being its budget; only a proof comes
             back as one ([ForkedQuery.valid_within]) *)
          let forked_native ~ms phi =
            match
              ForkedQuery.valid_within ~ms (fun () ->
                  native_check ~timeout:None phi)
            with
            | `Timeout ->
                Debug.print
                @@ lazy
                     (sprintf
                        "[no-unknown verdict] forked question killed, or not \
                         forked, after %d ms"
                        ms);
                `Timeout
            | (`Valid | `Unknown _) as r -> r
          in
          (* [native_check ~timeout phi] asked in a forked copy killed after
             [ms], and read as the in-process call would be read
             ([zero_unknown.external.fork_seqinst (Killed_after_budget
             {read_as_in_process})]).  The copy asks with no Z3 timer (the
             thread serving one does not exist in a forked process; the kill
             is the budget), [factor_eqs] with the budget it has in process.
             Contract: [`Valid] only if the copy answered valid, [`Invalid []]
             only if it answered invalid (its countermodel, a value of
             extensible variants, does not survive the trip back, so it is
             empty: no reader of the sequence instantiation reads one),
             [`Unknown r] for the copy's undecided answer [r], and [`Timeout]
             for a copy that timed out, was killed, died or raised; when no
             copy can be made (the memory budget, a pipe, other domains
             running) the call is made here, with its budget, exactly as
             without the fork.  So a question's answer differs from the
             in-process one only when the call does not return within [ms],
             which is where the in-process call overran its own budget.  With
             [quantified_only], a quantifier-free [phi] is asked here, as
             without the fork.  Each outcome is a phase-report event
             [seqinst-fork/...]. *)
          let forked_native_as_in_process ~ms ~timeout phi =
            if
              ZeroUnknownConfig.Switch.fork_seqinst_quantified_only
                config.zero_unknown
              && Ast.LogicOld.Formula.is_quantifier_free phi
            then (
              (* [quantified_only]: a quantifier-free form is asked here, the
                 call [`Not_forked] makes below *)
              Common.PhaseTime.event_here "seqinst-fork/here-qf";
              native_check ~timeout phi)
            else
            let factor_ms = Option.value timeout ~default:10000 in
            let outcome =
              ForkedQuery.run_forked ~ms (fun () ->
                  match native_check ~factor_ms ~timeout:None phi with
                  | `Valid -> `V
                  | `Invalid _ -> `I
                  | `Timeout -> `T
                  | `Unknown r -> `K r
                  | `Sat _ | `Unsat -> `K "unexpected answer")
            in
            Common.PhaseTime.event_here
              (match outcome with
              | `Value `V -> "seqinst-fork/valid"
              | `Value `I -> "seqinst-fork/invalid"
              | `Value `T -> "seqinst-fork/timeout"
              | `Value (`K r) ->
                  (* the reason's first words, so that the report tells a
                     solver's [unknown] from a refusal *)
                  "seqinst-fork/unknown:"
                  ^ String.prefix
                      (String.map r ~f:(fun c ->
                           if Char.is_alphanum c then c else '_'))
                      40
              | `Lost -> "seqinst-fork/killed"
              | `Not_forked -> "seqinst-fork/in-process");
            match outcome with
            | `Value `V -> `Valid
            | `Value `I -> `Invalid []
            | `Value `T | `Lost -> `Timeout
            | `Value (`K r) -> `Unknown r
            | `Not_forked -> native_check ~timeout phi
          in
          (* With COAR_PROBE_WEAKEN set in the environment, a validity
             question the ladder refuses is also handed to the weakened form
             ([WeakenedQuery.decide] on its negation, 2 s for the rest and for
             each dropped conjunct's check in a killed copy), and only which
             way it went is counted ([Common.PhaseTime.event_here]): the
             answer the ladder returns is the one it returned without the
             probe.  An instrument: it costs the probe's time and decides
             nothing. *)
          let probe_weakened phi =
            if Stdlib.(Sys.getenv_opt "COAR_PROBE_WEAKEN" <> None) then
              let neg = Ast.LogicOld.Formula.nnf_of (Ast.LogicOld.Formula.negate phi) in
              let res, _ =
                try
                  PCSatCommon.WeakenedQuery.decide ~id:None ~timeout:(Some 2000)
                    (Z3Smt.Z3interface.fenv_reached_by (Ast.LogicOld.get_fenv ()) neg)
                    neg
                with exn when not (Common.Timer.is_async exn) -> (None, "raised")
              in
              Common.PhaseTime.event_here
                (match res with
                | Some `Unsat -> "weaken-probe:valid"
                | Some (`Sat _) -> "weaken-probe:invalid"
                | _ -> "weaken-probe:undecided")
          in
          (* [zero_unknown.external.weaken_refused_ms]: a refused question
             [phi] is proved when the negation with its refused top-level
             conjuncts dropped is unsatisfiable.  Soundness, in the reading
             this verdict decides (a clause is valid when it holds in every
             model of the background theory, a term the theory leaves open
             taking every value): [nnf (not phi)] implies the conjunction
             [rest] of its other conjuncts, so a Z3 [unsat] of [rest] -- no
             model and no value of its free variables, uninterpreted symbols
             and open terms satisfying it -- is one of [not phi], which is
             exactly what [native_check] reads as [`Valid].  Nothing else is
             read from the weaker question: its model is not a countermodel of
             [phi], since a dropped conjunct may fail in it.  Each outcome is
             counted in the phase report ([weaken-refused:valid] or
             [:not-proved]). *)
          let weakened_proves ~timeout phi =
            match config.zero_unknown.external_.weaken_refused_ms with
            | None -> false
            | Some ms ->
                let proved =
                  PCSatCommon.WeakenedQuery.prove_refused ~id:None
                    ~budget:(Some (Int.min ms timeout)) phi
                in
                Common.PhaseTime.event_here
                  (if proved then "weaken-refused:valid"
                   else "weaken-refused:not-proved");
                proved
          in
          let fresh_body
              ?(native = fun ~timeout phi -> native_check ~timeout phi) timeout
              phi =
            let open Ast.LogicOld in
            pointwise_refute ~timeout phi
            @@ axioms_first
                 ~enabled:
                   (PCSatCommon.AxiomsFirst.After_fallback_proof.enabled
                      after_fallback_proof
                      ~fresh:
                        (ZeroUnknownConfig.Switch.seq_axioms_first_fresh
                           config.zero_unknown))
                 phi
            @@ fun phi ->
            let refused = Z3Smt.Z3interface.may_not_return phi in
            if refused then
              Debug.print
              @@ lazy
                   (sprintf
                      "[no-unknown verdict] refused for its binders: %s"
                      (String.concat ~sep:", "
                         (List.map
                            (Set.to_list
                               (Z3Smt.Z3interface.unsupported_binders phi))
                            ~f:(fun (x, s) ->
                              Ast.Ident.name_of_tvar x ^ ":"
                              ^ Ast.LogicOld.Term.str_of_sort s))));
            (* the fallback's own count, when the pair is chosen per question
               ([LadderSeqAxiomRlimit.for_fallback]); the solver was not asked
               a refused question unless a forked copy asked it *)
            let fallback_pair =
              LadderSeqAxiomRlimit.for_fallback
                ~refused_only:
                  (ZeroUnknownConfig.Switch.ladder_seq_axiom_rlimit_refused_only config.zero_unknown)
                ~per_node:(ZeroUnknownConfig.Switch.ladder_seq_axiom_units_per_node config.zero_unknown)
                ~only_attempt:
                  (refused
                  && Option.is_none
                       config.zero_unknown.external_.fork_refused_ms)
                ~size:
                  (match
                     (ZeroUnknownConfig.Switch.ladder_seq_axiom_units_per_node config.zero_unknown)
                   with
                  | None -> 0
                  | Some _ -> Formula.ast_size phi)
                (ZeroUnknownConfig.Switch.ladder_seq_axiom_rlimit config.zero_unknown)
            in
            ForkedQuery.fallback_unless_invalid
              ~skip:config.zero_unknown.axioms.invalid_skips_fallback
              ~fallback:(fun answer ->
                let r =
                  LadderSeqAxiomRlimit.with_ fallback_pair @@ fun () ->
                  Z3Smt.Z3interface.with_seq_axiom_fallback
                    ~caller_timeout:(Some timeout) ~id:None (get_fenv ()) phi
                    answer
                in
                (* the native question ran out of its budget and the
                   axiomatised form proved the question: the event
                   [axioms.first_after_fallback_proof] waits for *)
                if
                  PCSatCommon.AxiomsFirst.After_fallback_proof.note
                    after_fallback_proof ~asked_natively:(not refused)
                    ~native_ran_out:
                      (match answer with `Timeout -> true | _ -> false)
                    ~fallback_proved:
                      (match r with `Valid -> true | _ -> false)
                then (
                  Common.PhaseTime.event_here "axioms-first-from-here";
                  Debug.print
                  @@ lazy
                       "[no-unknown verdict] the native question ran out of \
                        its budget and the axiomatised form proved it: later \
                        fresh questions ask the axiomatised form first");
                (* counted only: a fallback question asked under the
                   per-question pair rather than the process-wide budget
                   (an undecided answer over a sequence is the only one the
                   fallback asks about); the answer is [r] either way *)
                (if
                   (!(Common.PhaseTime.on) || !(Common.PhaseTime.in_child))
                   && Option.is_some fallback_pair
                   && (match answer with
                      | `Valid | `Invalid _ -> false
                      | _ -> true)
                   && Ast.SeqAxiomEncoding.mentions_seq phi
                 then
                   Common.PhaseTime.event_here
                     (match r with
                     | `Valid -> "ladder-seq-axiom-rl/proved"
                     | _ -> "ladder-seq-axiom-rl/unproved"));
                r)
            @@
            if refused then (
              probe_weakened phi;
              if weakened_proves ~timeout phi then `Valid
              else
              match config.zero_unknown.external_.fork_refused_ms with
              | Some kill_ms -> forked_native ~ms:(Int.min kill_ms timeout) phi
              | None ->
                  `Unknown "not asked: the solver may not return on this shape")
            else native ~timeout:(Some timeout) phi
          in
          (* With [COAR_DUMP_LADDER_QUESTIONS=dir] in the environment, each
             fresh-context question of this ladder is written before it is
             asked as [dir/qN-PID_native.smt2] (the negation, whose [unsat]
             proves the question, so a question refused for its shape or cut
             short by the process's end can still be replayed alone), its
             outcome is appended to [dir/index.tsv], and [dir/stages.tsv]
             maps the file to the ladder's question number and stage.  A
             diagnostic: nothing is written and the answer is unchanged
             without the variable. *)
          let ask_fresh_within timeout phi =
            note_asking ~kind:"fresh" timeout phi;
            budgeted @@ fun () ->
            match Sys.getenv "COAR_DUMP_LADDER_QUESTIONS" with
            | None -> fresh_body timeout phi
            | Some dir ->
                Out_channel.with_file (dir ^ "/stages.tsv") ~append:true
                  ~f:(fun oc ->
                    Out_channel.output_string oc
                      (sprintf "q%d-%d\t%d\t%s\t%d\n"
                         (Atomic.get ladder_question_dump_count)
                         (Common.ForkGuard.self_pid ())
                         !budget_asked !ladder_phase
                         (Ast.LogicOld.Formula.ast_size phi)));
                let fenv = Ast.LogicOld.get_fenv () in
                Z3Smt.Z3interface.with_validity_dump ~native:false
                  ~var:"COAR_DUMP_LADDER_QUESTIONS"
                  ~counter:ladder_question_dump_count ~id:None ~timeout
                  ~outcome:(function
                    | `Valid -> "valid"
                    | `Invalid _ -> "invalid"
                    | _ -> "undecided")
                  fenv phi
                @@ fun () ->
                Z3Smt.Z3interface.dump_native_question ~id:None fenv phi;
                fresh_body timeout phi
          in
          let ask_fresh = ask_fresh_within config.zero_unknown.budgets.query_ms in
          let ask_clause_by_pieces ?(refine = contextual_in_place) ?unproved
              ~what ~ask c =
            ClausePieces.ask_by_pieces ~refine
              ?max:config.zero_unknown.pieces.bound ?unproved
              ~enabled:config.zero_unknown.pieces.split_clause_heads
              ~note:(fun msg ->
                Debug.print
                @@ lazy (sprintf "[no-unknown verdict] %s clause: %s" what msg))
              ~ask c
          in
          (* a rewritten clause asked by pieces, and, when that decides
             nothing and [contextual_extra] is on, asked once more in its
             contextual-ite form (with the refinement of an undecided piece
             that form was built with).  The first question is exactly the
             one asked without the extra form, so its answer is kept; the
             contextual form is equivalent to the clause in every model, so a
             proof or a refutation of it is one of the clause. *)
          (* [zero_unknown.guarded_facts]: a question the forward
             application of guarded hypotheses can act on is given to it,
             once per question.  The rule itself asks nothing, so a proof by
             the rule alone is taken before the question is asked.  In the
             quick sweep ([short = None]) a form it derives is asked before
             the question, whose own budget is already short; in the
             rewritten stages the question is first asked under
             [guarded_short_ms], and the form only when that leaves it
             undecided, then the question in full.  Only proofs are read.
             Why the two orders: the quick sweep stops at its overall
             deadline, so with the form behind each short question it reached
             the hard pieces' forms on none of the runs, and the rewritten
             stage then spent 50 s on the target; while forms asked before
             every rewritten piece cost an input whose pieces the solver
             decides in 2-3 s about 9 s more. *)
          let guarded_tried = Common.Ext.Hashtbl.PolyDeep.create () in
          let guarded_short_ms = 2000 in
          let guarded_first ?short ask phi =
            match (ZeroUnknownConfig.Switch.guarded_facts_ms config.zero_unknown) with
            | None -> ask phi
            | Some ms -> (
                let trace r =
                  Debug.print @@ lazy ("[no-unknown verdict] " ^ Lazy.force r)
                in
                let rule =
                  if
                    Hashtbl.mem guarded_tried phi
                    || not (PCSatCommon.GuardedFacts.applicable phi)
                  then `None
                  else (
                    Hashtbl.set guarded_tried ~key:phi ~data:();
                    Common.PhaseTime.with_phase "guarded-facts" (fun () ->
                        PCSatCommon.GuardedFacts.syntactic ~trace
                          ~theory_facts_only:
                            (ZeroUnknownConfig.Switch.guarded_facts_theory_facts_only config.zero_unknown)
                          phi))
                in
                match rule with
                | `Proved -> `Valid
                | `None -> ask phi
                | `Form psi -> (
                    let form_valid () =
                      Common.PhaseTime.with_phase "guarded-facts" (fun () ->
                          PCSatCommon.GuardedFacts.form_valid_forked ~trace ~ms
                            psi)
                    in
                    match short with
                    | None -> if form_valid () then `Valid else ask phi
                    | Some short -> (
                        match short phi with
                        | (`Valid | `Invalid _) as r -> r
                        | _ -> if form_valid () then `Valid else ask phi)))
          in
          let ask_rewritten_clause ?unproved ~what ~ask c =
            let ask =
              guarded_first ~short:(ask_fresh_within guarded_short_ms) ask
            in
            match ask_clause_by_pieces ?unproved ~what ~ask c with
            | (`Valid | `Invalid _) as r -> r
            | r when not contextual_extra -> r
            | r -> (
                let c' =
                  Ast.Evaluator.elim_onepoint_and_split_binders_contextual c
                in
                if Stdlib.( = ) c c' then r
                else
                  match
                    ask_clause_by_pieces ~refine:true
                      ~what:(what ^ ", contextual ite") ~ask c'
                  with
                  | (`Valid | `Invalid _) as r' -> r'
                  | _ -> r)
          in
          (* which clauses a question below has already shown valid, by
             index into [per_clause] (the rewritten forms are aligned with it,
             each equivalent to its original) *)
          let clause_valid = Array.create ~len:(List.length per_clause) false in
          (* With COAR_COUNT_LADDER_CLAUSES set in the environment, each
             clause this ladder newly shows valid is one phase-report event
             [ladder-clause-valid:I-of-N] (counted also when the run is
             stopped before the ladder returns).  An instrument: it decides
             nothing. *)
          let count_clauses =
            Stdlib.(Sys.getenv_opt "COAR_COUNT_LADDER_CLAUSES" <> None)
          in
          let mark_valid i =
            if not clause_valid.(i) then (
              clause_valid.(i) <- true;
              if count_clauses then
                Common.PhaseTime.event_here
                  (sprintf "ladder-clause-valid:%d-of-%d" i
                     (Array.length clause_valid)))
          in
          (* [zero_unknown.congruence_match]: a clause whose conclusion is
             its own premises up to their equalities is proved without a
             solver ([CongruenceMatch.valid], which reads only proofs and
             interprets no symbol); skipped where only a refutation is read.
             A phase-report event per clause proved, and a failure inside
             the match (a formula [nnf_of] does not take) proves nothing. *)
          if
            config.zero_unknown.congruence_match
            && not !PCSatCommon.ShapeProof.refutation_only
          then
            Common.PhaseTime.with_phase "congruence-match" (fun () ->
                List.iteri per_clause ~f:(fun i c ->
                    if
                      (not clause_valid.(i))
                      &&
                      try PCSatCommon.CongruenceMatch.valid c
                      with exn_ when not (Common.Timer.is_async exn_) ->
                        false
                    then (
                      Common.PhaseTime.event "congruence-match/proved";
                      Debug.print
                      @@ lazy
                           (sprintf
                              "[no-unknown verdict] clause %d: proved by \
                               congruence match"
                              i);
                      mark_valid i)));
          (* skipped where only a refutation is read: a proof of validity
             refutes nothing (see [ShapeProof.with_refutation_only]) *)
          Option.iter
            (if !PCSatCommon.ShapeProof.refutation_only then None
             else (ZeroUnknownConfig.Switch.shape_proof_ms config.zero_unknown)) ~f:(fun ms ->
              Common.PhaseTime.with_phase "shape-proof" @@ fun () ->
              List.iteri per_clause ~f:(fun i c ->
                  if
                    (not clause_valid.(i))
                    && PCSatCommon.ShapeProof.valid_within
                         ~print:(fun m ->
                           Debug.print
                           @@ lazy
                                (sprintf "[no-unknown verdict] clause %d: %s" i
                                   (Lazy.force m)))
                         ~fork:false
                         ~literal_closures:
                           ( (ZeroUnknownConfig.Switch.shape_proof_literal_closures config.zero_unknown),
                             (ZeroUnknownConfig.Switch.shape_proof_literal_closure_ms config.zero_unknown) )
                         ~ms ~id:!id c
                  then mark_valid i));
          Debug.print
          @@ lazy
               (sprintf "[no-unknown verdict] %d clause(s), sizes %s"
                  (List.length per_clause)
                  (String.concat ~sep:" "
                  @@ List.map per_clause ~f:(fun c ->
                         string_of_int (Ast.LogicOld.Formula.ast_size c))));
          (* Under [zero_unknown.pieces.remember_proved]: for a rewritten
             clause asked by its pieces and not shown valid, the conjunction of
             the pieces left undecided (every other piece was shown valid), by
             the same index.  Valid exactly when the rewritten clause is, so a
             later stage may ask it in the clause's place. *)
          let remember = config.zero_unknown.pieces.remember_proved in
          let residual = Array.create ~len:(List.length per_clause) None in
          (* [ClausePieces.ask_by_pieces] gives the undecided pieces only
             when some piece or sub-piece was shown valid, and gives an
             undecided piece's undecided sub-pieces in its place: with every
             piece undecided the conjunction is the clause again, and a
             conjunction of coarse pieces is a form the sequence
             instantiation splits worse than the clause -- it splits a
             conjunction only while its conjuncts' own pieces number at most
             its bound, so such a residual was asked as one piece where the
             clause split into dozens, each decided in a fraction of a second
             (measured: a satisfiable input proved by 36 pieces at 21 s left
             undecided at the time limit). *)
          let unproved_of i =
            if remember then
              Some
                (fun ps ->
                  Debug.print
                  @@ lazy
                       (sprintf
                          "[no-unknown verdict] clause %d: %d pieces left \
                           undecided, remembered"
                          i (List.length ps));
                  residual.(i) <- Some (Ast.LogicOld.Formula.and_of ps))
            else None
          in
          (* a rewritten clause, or what is left of it to prove *)
          let left_of i c = Option.value residual.(i) ~default:c in
          (* The last question on the satisfiable side, asked only when every
             one above is undecided: each clause not yet shown valid is asked
             again after its sequence binders, and in the forms asked first
             its integer binders too, are instantiated where that only
             strengthens it ([NoUnknownSeqInst]), so a [`Valid] for every
             clause is a proof of validity, while any other answer is
             discarded and the undecided answer stands.  The instantiated
             clause is asked like the rewritten ones -- the exact rewrites
             applied once more, since instantiation exposes new definitions,
             then a fresh context -- and it is refused like them if it still
             binds a sequence. *)
          set_seq_instantiation_switches ();
          let seq_instantiation undecided =
            let ask_form ask_fresh c =
              let c =
                if config.zero_unknown.rewrites.onepoint.split then
                  Ast.Evaluator.elim_onepoint_and_split_binders c
                else c
              in
              let r = ask_fresh c in
              Debug.print
              @@ lazy
                   (sprintf
                      "[no-unknown verdict] sequence-instantiated clause \
                       %s: size %d: %s"
                      (match r with
                      | `Valid -> "valid"
                      | `Invalid _ -> "invalid (says nothing)"
                      | `Timeout -> "timeout"
                      | `Unknown reason -> reason
                      | `Sat _ | `Unsat -> "unexpected")
                      (Ast.LogicOld.Formula.ast_size c)
                      (* a bounded prefix: these forms reach half a million
                         nodes, and printing one whole took 10-15 s *)
                      (Ast.LogicOld.Formula.str_of_prefix c));
              r
            in
            (* With [zero_unknown.budgets.two_pass_ms], every form is asked
               first at the short budget and only the ones that ran out of it
               again at the full one; see [first_proved]. *)
            (* With [zero_unknown.external.fork_seqinst], a form is asked
               in a forked copy killed at the larger of the field and the
               question's budget (at the budget plus a margin with
               [zero_unknown.external.fork_seqinst (Killed_after_budget)], so that the
               first pass's short budget holds in the copy too); only the
               verdict comes back, and anything but
               [`Valid] is reported as undecided, which [prove_valid] reads as
               it reads every answer but [`Valid] -- or, with
               [read_as_in_process], every answer is read as in process and
               a question no copy can be made for is asked here
               ([forked_native_as_in_process]) *)
            let fresh_within =
              match (ZeroUnknownConfig.Switch.fork_seqinst_questions config.zero_unknown) with
              | None -> ask_fresh_within
              | Some kill_ms ->
                  fun timeout phi ->
                    let ms =
                      ForkedQuery.ladder_kill_ms ~floor:kill_ms
                        ~margin:(ZeroUnknownConfig.Switch.fork_seqinst_kill_margin config.zero_unknown)
                        ~timeout
                    in
                    (* only the solver call is forked, and asked there with no
                       Z3 timer (the thread serving it does not exist in a
                       forked process), the kill being its budget; the shape
                       test and the sequence-axiom fallback stay in-process, as
                       without the field *)
                    let native =
                      if
                        ZeroUnknownConfig.Switch.fork_seqinst_read_as_in_process
                          config.zero_unknown
                      then forked_native_as_in_process ~ms
                      else fun ~timeout:_ phi ->
                        (* rebuilt, so that its type is open as the other
                           branch's is *)
                        match forked_native ~ms phi with
                        | `Valid -> `Valid
                        | `Timeout -> `Timeout
                        | `Unknown r -> `Unknown r
                    in
                    note_asking ~kind:"forked" timeout phi;
                    budgeted @@ fun () -> fresh_body ~native timeout phi
            in
            let ask, second_pass =
              match config.zero_unknown.budgets.two_pass_ms with
              | None ->
                  ( ask_form (fresh_within config.zero_unknown.budgets.query_ms),
                    None )
              | Some ms ->
                  ( ask_form (fresh_within ms),
                    Some
                      ( (function `Timeout -> true | _ -> false),
                        ask_form (fresh_within config.zero_unknown.budgets.query_ms)
                      ) )
            in
            SeqInstantiation.form_built_trace :=
              (fun secs form ->
                Debug.print
                @@ lazy
                     (sprintf
                        "[no-unknown verdict] form built in %.2f s: %s, at \
                         %.2f s"
                        secs
                        (match form with
                        | None -> "none"
                        | Some f ->
                            sprintf "size %d"
                              (Ast.LogicOld.Formula.ast_size f))
                        (Common.Clock.now_s () -. ladder_t0)));
            SeqInstantiation.clause_trace :=
              (fun msg ->
                Debug.print
                @@ lazy
                     (sprintf "[no-unknown verdict] seqinst %s, at %.2f s"
                        (Lazy.force msg)
                        (Common.Clock.now_s () -. ladder_t0)));
            (* With [zero_unknown.case_split_index (Index_cases budget_ms)], the index-case
               questions are asked at that budget (never above the form's own),
               so that a case the solver decides only slowly counts as
               undecided and the form is then asked whole; reset on the way
               out, so that no later ladder asks with this one's solver *)
            SeqInstantiation.index_case_ask :=
              Option.map (ZeroUnknownConfig.Switch.case_split_index_budget config.zero_unknown)
                ~f:(fun ms ->
                  let ask_case =
                    ask_form
                      (fresh_within
                         (Int.min ms config.zero_unknown.budgets.query_ms))
                  in
                  fun phi ->
                    match ask_case phi with
                    | `Valid -> `Valid
                    | `Invalid _ -> `Invalid ()
                    | _ -> `Undecided);
            let result =
              Exn.protect
                ~finally:(fun () -> SeqInstantiation.index_case_ask := None)
                ~f:(fun () ->
                  NoUnknownSeqInst.prove_valid ?second_pass
                    ~schedule:remember
                    ~proved:mark_valid
                    ~enabled:
                      config.zero_unknown.seq_instantiation.premises
                    ~already_valid:(fun i -> clause_valid.(i))
                    ~ask
                    (match per_clause_rewritten with
                    | Some rewritten when remember ->
                        List.mapi rewritten ~f:left_of
                    | Some rewritten -> rewritten
                    | None -> per_clause))
            in
            GroupDebug.print
              @@ lazy
                   (sprintf
                      "[no-unknown verdict] grouped piece questions: %d \
                       asked, %d proved, %d pieces proved by them; %d \
                       pieces proved before grouping; %d by lead forms \
                       outside a grouped question; %d groups led past the \
                       lead bound"
                      !SeqInstantiation.group_questions_asked
                      !SeqInstantiation.group_questions_proved
                      !SeqInstantiation.group_pieces_proved
                      !SeqInstantiation.lead_forms_pieces_proved
                      !SeqInstantiation.lead_forms_unasked_proved
                      !SeqInstantiation.lead_forms_open_gated_groups);
            match result with
            | `Valid -> `Valid
            | `Undecided -> undecided
          in
          (* The quick sweep (see [zero_unknown.budgets.quick_sweep]): every
             clause, piece by piece, at a short budget, stopping at the first
             refutation; a clause whose pieces are all shown valid is recorded.
             Asked exactly as the long questions below ask ([ask]), only with a
             smaller budget, so an answer here is one of theirs. *)
          let quick_sweep () =
            match (ZeroUnknownConfig.Switch.quick_sweep config.zero_unknown) with
            | None -> None
            | Some (per_query, whole) ->
                enter_phase "quick";
                let deadline =
                  Common.Clock.now_s () +. (Float.of_int whole /. 1000.)
                in
                (* [COAR_DUMP_QUICK_SWEEP=dir] (instrument only): each piece
                   the sweep asks is written as [dir/sN-PID_native.smt2], its
                   negation, and every solver check made while it is asked
                   under the prefix [dir/sN-PID] (the sequence-axiom fallback's
                   included); nothing is written and nothing changes without
                   the variable. *)
                let quick_dumped = ref 0 in
                let ask_short_body ?(fresh = false) phi = budgeted @@ fun () ->
                  pointwise_refute ~timeout:per_query phi
                  @@ axioms_first phi @@ fun phi ->
                  let phi = factor_eqs ~timeout:per_query phi in
                  (if config.zero_unknown.rewrites.seq_as_array then
                     Z3Smt.Z3interface.check_valid_seq_as_array
                   else Z3Smt.Z3interface.check_valid)
                    ~timeout:(Some per_query) ~fresh_solver:fresh ~id:None
                    (Ast.LogicOld.get_fenv ()) phi
                in
                (* [budgets.quick_sweep.plain_retry]: a piece [phi] left
                   undecided above, whose question the integer-binder split
                   in force would change, is asked again by the same route
                   and under the same budget with the split off, in a fresh
                   solver context (one that holds only this question).
                   Assumes: [phi] is the piece's validity question, as
                   above.  Guarantees: [`Valid] or [`Invalid m] only when
                   one of the two asks returned it about [phi] (the split is
                   an equivalence in every model with no fresh free
                   variable, so the split and plain questions have the same
                   valid and invalid instances, and a countermodel of
                   either is one of [phi]); the first ask's answer
                   otherwise.  Both asks go through [check_valid] (or its
                   sequences-as-arrays twin), so the negation is built,
                   interpretation-dependent terms are encoded and the
                   sequence-axiom fallback is applied the same way in both.
                   Each retry is one phase-report event
                   [quick-plain-retry:valid|invalid|undecided].  Why: the
                   split is wanted where a read at [x - c] needs an instance
                   no trigger produces, yet on one piece over a
                   concatenation's range tests the split form was left
                   undecided by Z3 5.1.0 past 20 s under three seeds while
                   the plain form was unsatisfiable in 0.08 s; asked in the
                   sweep's pooled context, which holds the earlier pieces'
                   declarations, the plain form was proved within the 500 ms
                   budget in only about half of the asks, and in a fresh
                   context in every one. *)
                let ask_short_body phi =
                  match ask_short_body ~fresh:false phi with
                  | (`Valid | `Invalid _) as r -> r
                  | r
                    when (not
                            (ZeroUnknownConfig.Switch.quick_sweep_plain_retry
                               config.zero_unknown))
                         || not
                              (Z3Smt.Z3interface.split_int_binders_would_change
                                 phi) ->
                      r
                  | r -> (
                      let r' =
                        Z3Smt.Z3interface.without_split_int_binders (fun () ->
                            ask_short_body ~fresh:true phi)
                      in
                      Common.PhaseTime.event_here
                        (match r' with
                        | `Valid -> "quick-plain-retry:valid"
                        | `Invalid _ -> "quick-plain-retry:invalid"
                        | _ -> "quick-plain-retry:undecided");
                      match r' with (`Valid | `Invalid _) -> r' | _ -> r)
                in
                let ask_short phi =
                  match Sys.getenv "COAR_DUMP_QUICK_SWEEP" with
                  | None -> ask_short_body phi
                  | Some dir ->
                      let prefix =
                        sprintf "%s/s%d-%d" dir !quick_dumped
                          (Common.ForkGuard.self_pid ())
                      in
                      incr quick_dumped;
                      Z3Smt.Z3interface.with_query_dump prefix (fun () ->
                          Z3Smt.Z3interface.dump_native_question ~id:None
                            (Ast.LogicOld.get_fenv ()) phi;
                          ask_short_body phi)
                in
                NoUnknownLadder.quick_sweep
                  ~finish_started_clause:
                    (ZeroUnknownConfig.Switch.quick_sweep_finish_clause config.zero_unknown)
                  ~past_deadline:(fun () ->
                    Float.(Common.Clock.now_s () >= deadline))
                  ~pieces_of:(fun c ->
                    if config.zero_unknown.pieces.split_clause_heads then
                      match ClausePieces.of_clause c with
                      | [] -> [ c ]
                      | ps -> ps
                    else [ c ])
                  ~ask:(guarded_first ask_short) ~mark_valid
                  ~on_piece:(fun i p ->
                    Debug.print
                    @@ lazy
                         (sprintf
                            "[no-unknown verdict] quick sweep: clause %d, a \
                             piece of size %d"
                            i (Ast.LogicOld.Formula.ast_size p)))
                  ~on_refuted:(fun i ->
                    Debug.print
                    @@ lazy
                         (sprintf
                            "[no-unknown verdict] quick sweep: clause %d \
                             refuted"
                            i))
                  per_clause
          in
          let pieces_first () =
            match (ZeroUnknownConfig.Switch.pieces_first config.zero_unknown) with
            | None -> None
            | Some pf ->
                let pf = PCSatCommon.ValidityAsk.pieces_first_of_pair pf in
                enter_phase "pieces-first";
                (* each piece: the shape test, then natively in a fresh
                   context under the piece budget (never forked: the ladder's
                   stage has no fork policy), then by cvc5 under its piece
                   budget; inside the ladder's [budgeted] like every other
                   question it asks *)
                let ask p =
                  budgeted @@ fun () ->
                  let fenv = Ast.LogicOld.get_fenv () in
                  let r =
                    PCSatCommon.ValidityAsk.ask_piece
                      ~native:(fun p ->
                        PCSatCommon.ValidityAsk.check_valid ~margin_ms:None
                          ~timeout:pf.z3_ms ~fresh_solver:true ~id:None fenv p)
                      ~cvc5:
                        (PCSatCommon.ValidityAsk.cvc5_of_pieces_first pf
                           ~rlimit:None ~site:"ladder-pieces"
                           ~phase:"pieces-first-cvc5")
                      ~id:None fenv p
                  in
                  Debug.print
                  @@ lazy
                       (sprintf
                          "[no-unknown verdict] pieces first: a piece of size %d %s"
                          (Ast.LogicOld.Formula.ast_size p)
                          (match r with
                          | `Valid -> "valid"
                          | `Invalid _ -> "invalid"
                          | _ -> "undecided"));
                  r
                in
                List.find_mapi per_clause ~f:(fun i c ->
                    if clause_valid.(i) then None
                    else
                      match PCSatCommon.ValidityAsk.prove_pieces ~ask c with
                      | `Valid ->
                          Debug.print
                          @@ lazy
                               (sprintf
                                  "[no-unknown verdict] pieces first: clause %d valid"
                                  i);
                          mark_valid i;
                          None
                      | `Invalid model -> Some (`Invalid model)
                      | `Rest (_, proved, total) ->
                          (* the clause is left to the stages below whole:
                             the conjunction of its pieces left is not always
                             the easier question *)
                          Debug.print
                          @@ lazy
                               (sprintf
                                  "[no-unknown verdict] pieces first: clause %d, %d of %d pieces valid"
                                  i proved total);
                          None
                      | `Unsplit -> None)
          in
          (* The questions [zero_unknown.early_stage.exact_forms_first] moves ahead of
             the long unrewritten ones: each clause not yet shown valid asked in
             its rewritten form, piece by piece, then the sequence instantiation.
             Every answer taken from them is one the ladder below would take
             from the same question later -- a refutation only from an exact
             rewrite, a proof only of validity -- so moving them changes which
             answer is reached within the time, never which answer is right. *)
          let exact_forms_first () =
            if not config.zero_unknown.early_stage.exact_forms_first then None
            else
              let () = enter_phase "early-rewritten" in
              (* at the short budget under [zero_unknown.budgets.two_pass_ms]:
                 a piece that runs out of it is asked again at the full budget
                 by the rewritten pass further down, which every run reaches
                 when nothing before it decides *)
              let ask_early =
                match config.zero_unknown.budgets.two_pass_ms with
                | None -> ask_fresh
                | Some ms -> ask_fresh_within ms
              in
              (* the question asked of a skipped clause under
                 [zero_unknown.early_stage.rewritten.refute_skipped]: the pass's
                 own fresh question at its own budget, without the proof-only
                 word forms added below, since only a refutation is read *)
              let ask_skipped = ask_early in
              (* [zero_unknown.rewrites.decided_forms]: the piece with the
                 contextual [ite] rule applied (exact), its two-round
                 matched-instance form ([word_forms ~two_rounds_first:true]'s
                 first; it implies the piece), after the exact one-point
                 rule, with the integer atoms its own integer facts decide
                 replaced by their values ([EntailedAtoms.decide], an
                 equivalence), asked natively in a context of its own.  Only a
                 proof is read: the form implies the piece *)
              let entailed_memo = Common.Ext.Hashtbl.PolyDeep.create () in
              let decided_form_proved phi =
                (* the pieces of one clause share their premises, so the same
                   entailment is asked again and again; its answer is a
                   function of the two formulas and kept *)
                let entails l a =
                  match Hashtbl.find entailed_memo (l, a) with
                  | Some b -> b
                  | None ->
                  let b =
                  try
                    match
                      Z3Smt.Z3interface.with_rlimit
                        (Some (ZeroUnknownConfig.Switch.decided_forms_rlimit config.zero_unknown))
                        (fun () ->
                          Z3Smt.Z3interface.check_sat
                            ~timeout:(Some config.zero_unknown.budgets.query_ms)
                            ~id:None (Ast.LogicOld.get_fenv ())
                            [ l; Ast.LogicOld.Formula.negate a ])
                    with
                    | `Unsat -> true
                    | _ -> false
                  with exn when not (Common.Timer.is_async exn) -> false
                  in
                  Hashtbl.set entailed_memo ~key:(l, a) ~data:b;
                  b
                in
                let piece =
                  NoUnknownSeqInst.prepare_piece
                    (Ast.Evaluator.elim_onepoint_and_split_binders_contextual
                       phi)
                in
                match
                  NoUnknownSeqInst.word_forms ~two_rounds_first:true piece
                with
                | [] -> false
                | form :: _ -> (
                    match
                      (try Lazy.force form
                       with exn when not (Common.Timer.is_async exn) -> None)
                    with
                    | None -> false
                    | Some c ->
                        let c = Ast.Evaluator.elim_onepoint_and_split_binders c in
                        if
                          not
                            (Set.is_empty
                               (Ast.LogicOld.Formula.quantified_sort_env_of c))
                        then false
                        else
                          let c' =
                            Common.PhaseTime.with_phase "decided-form" (fun () ->
                                PCSatCommon.EntailedAtoms.decide ~entails c)
                          in
                          Debug.print
                          @@ lazy
                               (sprintf
                                  "[no-unknown verdict] decided form: size %d \
                                   -> %d"
                                  (Ast.LogicOld.Formula.ast_size c)
                                  (Ast.LogicOld.Formula.ast_size c'));
                          match ask_fresh c' with `Valid -> true | _ -> false)
              in
              (* Unless [zero_unknown.words] is
                 [No_word_instances], each question of this pass is asked first
                 through the words of its quantifier-free matched-instance forms
                 (each a strengthening, and the words question weaker than its
                 form, so only a proof is read), then as it is *)
              let ask_early =
                match config.zero_unknown.words with
                | No_word_instances -> ask_early
                | (One_round_first | Two_rounds_first) as word_instances ->
                fun phi ->
                  (* A form substitutes terms of [phi] for its binders, so it
                     reads an integer as a word only if [phi] already does;
                     without such a read no form can be asked as a words
                     question, and building them (every piece, two rounds of
                     matching) cost 60-75 s on an input with no [int_to_bv],
                     every form discarded unasked *)
                  if not (Z3Smt.Z3interface.reads_int_as_word phi) then
                    ask_early phi
                  else
                  let piece = NoUnknownSeqInst.prepare_piece phi in
                  (* the plain matched forms, then two rounds of matching: an
                     index the goal reaches only through a premise's instance
                     (a word read at [i div 64] once a bit fact is instantiated
                     at [i]) is matched in the second round *)
                  let forms =
                    NoUnknownSeqInst.word_forms
                      ~two_rounds_first:
                        (match word_instances with
                        | Two_rounds_first -> true
                        | One_round_first | No_word_instances -> false)
                      piece
                  in
                  let by_words c =
                    let c =
                      if config.zero_unknown.rewrites.onepoint.split then
                        Ast.Evaluator.elim_onepoint_and_split_binders c
                      else c
                    in
                    if
                      Z3Smt.Z3interface.reads_int_as_word c
                      && Set.is_empty
                           (Ast.LogicOld.Formula.quantified_sort_env_of c)
                    then (
                      note_asking ~kind:"words" config.zero_unknown.budgets.query_ms
                        c;
                      budgeted @@ fun () ->
                      Z3Smt.Z3interface.check_valid_by_words
                        ~timeout:(Some config.zero_unknown.budgets.query_ms)
                        ~id:None
                        (Ast.LogicOld.get_fenv ())
                        c)
                    else `Unknown "not a quantifier-free word question"
                  in
                  if NoUnknownSeqInst.first_proved_formula ~ask:by_words forms
                  then (
                    Debug.print
                    @@ lazy
                         "[no-unknown verdict] early question proved through \
                          the words of a matched-instance form";
                    `Valid)
                  else if
                    (ZeroUnknownConfig.Switch.decided_forms config.zero_unknown)
                    && ((* counted so that a run can be told to have reached
                          this question; nothing else is changed *)
                        Common.PhaseTime.event_here "decided-form-tried";
                        decided_form_proved phi)
                  then (
                    Debug.print
                    @@ lazy
                         "[no-unknown verdict] early question proved through \
                          its decided form";
                    `Valid)
                  else ask_early phi
              in
              let refuted =
                (match config.zero_unknown.early_stage.rewritten.full_major_every with
                | Some n -> Z3Smt.Z3interface.with_new_context_full_major_every n
                | None -> fun f -> f ())
                @@ fun () ->
                match per_clause_rewritten with
                | None -> None
                | Some rewritten ->
                    List.find_mapi rewritten ~f:(fun i c ->
                        if clause_valid.(i) then None
                        else
                          match
                            ClausePieces.early_question
                              ?max:config.zero_unknown.pieces.bound
                              ~within_refinement:
                                config.zero_unknown.early_stage.rewritten.within_refinement
                              ~max_pieces:
                                config.zero_unknown.early_stage.rewritten.max_pieces
                              ~refute_skipped:
                                config.zero_unknown.early_stage.rewritten.refute_skipped
                              ~ask_whole:(fun c ->
                                Common.PhaseTime.with_phase
                                  (sprintf "clause-%d-refute" i)
                                @@ fun () -> ask_skipped c)
                              ~ask_pieces:(fun c ->
                                Common.PhaseTime.with_phase
                                  (sprintf "clause-%d" i)
                                @@ fun () ->
                                ask_rewritten_clause ?unproved:(unproved_of i)
                                  ~what:"rewritten (early)" ~ask:ask_early c)
                              c
                          with
                          | `Skipped (Some model) ->
                              (* counted in both cases, so that a run can be
                                 told to have skipped a clause *)
                              Common.PhaseTime.event_here
                                (sprintf "clause-%d-skipped" i);
                              Debug.print
                              @@ lazy
                                   (sprintf
                                      "[no-unknown verdict] early rewritten \
                                       pass: clause %d skipped for its pieces \
                                       and refuted by its one question"
                                      i);
                              Some (`Invalid model)
                          | `Skipped None ->
                              Common.PhaseTime.event_here
                                (sprintf "clause-%d-skipped" i);
                              Debug.print
                              @@ lazy
                                   (sprintf
                                      "[no-unknown verdict] early rewritten \
                                       pass: clause %d left to the sequence \
                                       instantiation"
                                      i);
                              None
                          | `Asked (`Invalid model) -> Some (`Invalid model)
                          | `Asked `Valid ->
                              mark_valid i;
                              None
                          | `Asked _ -> None)
              in
              match refuted with
              | Some verdict -> Some verdict
              | None when Array.for_all clause_valid ~f:Fn.id -> Some `Valid
              | None
                when not
                       (PCSatCommon.NoUnknownLadder.seq_instantiation_read
                          !PCSatCommon.NoUnknownLadder.read) ->
                  (* a proof only, and the caller reads only a refutation *)
                  Common.PhaseTime.event_here "early-seqinst-not-read";
                  None
              | None -> (
                  enter_phase "early-seqinst";
                  match seq_instantiation `Undecided with
                  | `Valid -> Some `Valid
                  | _ -> None)
          in
          (* The sequence-length strengthening, tried only where the answer
             is otherwise [unknown] or [timeout] (see [NoUnknownSeqPin]).  It
             is given the clauses as they stand, not the rewritten forms asked
             above: one of those rewrites is exact only for validity, and a
             countermodel of the rewritten clause need not be one of the
             original.  The query is asked in a fresh context told only the
             definitions it reaches, for the reasons given at [fenv_used_by],
             under the array side's budget.
             The three pins below take [within], which gives the budget of
             the next question in milliseconds, or [None] when the pin's time
             is spent and the question is not asked: the late pins at the end
             of the ladder always have [zero_unknown.budgets.refutation_ms]; the
             early pins ([zero_unknown.early_stage.pins]) have a smaller one and
             a deadline. *)
          let seq_pin_refutation ~within ?expired:_ ?(early = false) () =
            let applicable =
              early && (ZeroUnknownConfig.Switch.early_pins_require_applicable config.zero_unknown)
            in
            let guess_question psi =
              match within () with
              | None -> `Undecided
              | Some timeout -> (
                  let r =
                    Z3Smt.Z3interface.with_rlimit ~label:"ladder"
                      config.zero_unknown.budgets.query_rlimit
                    @@ fun () ->
                    Z3Smt.Z3interface.check_sat ~timeout:(Some timeout)
                      ~fresh_solver:true ~id:None (fenv_used_by psi) [ psi ]
                  in
                  Debug.print
                  @@ lazy
                       (sprintf
                          "[no-unknown verdict] sequence-length guess from \
                           the relaxation: %s"
                          (match r with
                          | `Sat _ -> "a model (lengths read)"
                          | `Unsat -> "unsat"
                          | `Timeout -> "timeout"
                          | `Unknown reason -> "unknown: " ^ reason));
                  match r with
                  | `Sat model -> `Model model
                  | `Unsat -> `Unsat
                  | _ -> `Undecided)
            in
            NoUnknownSeqPin.refute
              ~fixed_per_clause:
                (ZeroUnknownConfig.Switch.seq_pin_fixed_lengths_per_clause config.zero_unknown)
              ?askable:
                (if (ZeroUnknownConfig.Switch.pin_seq_lengths_asked_shapes_only config.zero_unknown)
                 then
                   Some
                     (fun psi ->
                       let refused = Z3Smt.Z3interface.may_not_return psi in
                       (* counted for the act set of a batch: a pinned
                          negation the pin would have asked without the
                          switch; raised after the decision, changing none *)
                       if refused then
                         Common.PhaseTime.event_here "askpin-not-asked";
                       if refused then
                         Debug.print
                         @@ lazy
                              "[no-unknown verdict] sequence-pinned query: \
                               not asked (it binds a sequence under a \
                               quantifier)";
                       not refused)
                 else None)
              ~enabled:(ZeroUnknownConfig.Switch.pin_seq_lengths config.zero_unknown)
              ?already_valid:
                (if applicable
                    || ((not early)
                       && (ZeroUnknownConfig.Switch.late_seq_pin_skips_proved_clauses config.zero_unknown))
                 then
                   Some
                     (fun i -> i < Array.length clause_valid && clause_valid.(i))
                 else None)
              ?classify:
                (if applicable && (ZeroUnknownConfig.Switch.pin_seq_lengths_from_model config.zero_unknown)
                 then Some guess_question
                 else None)
              ?guess:
                (if (ZeroUnknownConfig.Switch.pin_seq_lengths_from_model config.zero_unknown)
                    && not applicable then
                   Some
                     (fun psi ->
                       match within () with
                       | None -> None
                       | Some timeout -> (
                           let r =
                             Z3Smt.Z3interface.with_rlimit
                               ~label:"ladder"
                               config.zero_unknown.budgets.query_rlimit
                             @@ fun () ->
                             Z3Smt.Z3interface.check_sat
                               ~timeout:(Some timeout) ~fresh_solver:true
                               ~id:None (fenv_used_by psi) [ psi ]
                           in
                           Debug.print
                           @@ lazy
                                (sprintf
                                   "[no-unknown verdict] sequence-length \
                                    guess from the relaxation: %s"
                                   (match r with
                                   | `Sat _ -> "a model (lengths read)"
                                   | `Unsat -> "unsat"
                                   | `Timeout -> "timeout"
                                   | `Unknown reason -> "unknown: " ^ reason));
                           match r with `Sat model -> Some model | _ -> None))
                 else None)
              ~ask:(fun psi ->
                match within () with
                | None -> None
                | Some timeout ->
                Debug.print
                @@ lazy
                     (sprintf "[no-unknown verdict] sequence-pinned query \
                               of size %d, binding a sequence: %b"
                        (Ast.LogicOld.Formula.ast_size psi)
                        (Z3Smt.Z3interface.may_not_return psi));
                let in_process ~timeout =
                  Z3Smt.Z3interface.with_rlimit ~label:"ladder" config.zero_unknown.budgets.query_rlimit
                  @@ fun () ->
                  Z3Smt.Z3interface.check_sat
                    ~timeout ~fresh_solver:true ~id:None (fenv_used_by psi) [ psi ]
                in
                (* [pins.seq_lengths.fork_unreturning]: a pinned negation of
                   a shape on which Z3 may ignore its own [timeout]
                   ([Z3interface.may_ignore_timeout]: a quantifier binding a
                   sequence, or any quantifier in a question that reads a
                   sequence) is asked first in a forked copy killed after the
                   question's budget ([ForkedQuery.first_in_copy]): one such
                   negation, the same formula up to the names of its
                   uninterpreted sorts as one Z3 answered [unsat] in 0.5 s,
                   ran past 60 s and 5 GB in process until the memory cap
                   killed the run.  [sat] is asked again here for its model,
                   so a refutation is always an in-process [sat], as without
                   the field; a copy that runs out, dies or raises leaves the
                   question undecided, which the pin reads as it reads a
                   timeout.  A workaround for an external defect: Z3 5.1.0
                   ignores its timeout on such a query in a context that has
                   been in a scope, and whether it does can depend only on the
                   uninterpreted sort names.  It is fixed upstream in Z3 5.3.3
                   (and the 5.3.4 nightly), but the newest Z3 in
                   opam-repository is 5.1.0, so the workaround stays until
                   opam provides a fixed Z3.  Remove the field and this branch,
                   with [preprocessor.elimination.questions.fork.seq_unreturning],
                   when the row for
                   [benchmarks/SMT/simple/z3_seq_pin_scoped_timeout_unsat.smt2]
                   in [script/rerun_external_reproducers.sh] reports GONE for
                   the Z3 that opam installs. *)
                let r =
                  if (ZeroUnknownConfig.Switch.pin_seq_lengths_fork_unreturning config.zero_unknown)
                     && Z3Smt.Z3interface.may_ignore_timeout psi
                  then
                    PCSatCommon.ForkedQuery.first_in_copy ~copy_timeout:None ~ms:timeout
                      ~event:"seqpin-fork" ~ask:in_process ~lost:`Timeout
                      ~here_for:(function `Sat _ -> true | _ -> false)
                      ~label:(function
                        | `Sat _ -> "sat"
                        | `Unsat -> "unsat"
                        | `Unknown _ -> "unknown"
                        | `Timeout -> "lost")
                  else in_process ~timeout:(Some timeout)
                in
                Debug.print
                @@ lazy
                     (sprintf "[no-unknown verdict] sequence-pinned query: %s"
                        (match r with
                        | `Sat _ -> "sat (a refutation)"
                        | `Unsat -> "unsat (says nothing)"
                        | `Timeout -> "timeout"
                        | `Unknown reason -> "unknown: " ^ reason));
                match r with `Sat model -> Some model | _ -> None)
              (Set.to_list @@ Ast.ClauseSetOld.to_formulas
              @@ Ast.ClauseSet.to_old_clause_set Map.Poly.empty
              @@ PCSP.Problem.clauses_of pcsp)
          in
          (* The point pin (see [NoUnknownScalarPin]), tried after the
             sequence-length pin.  Like it, it is given the clauses as they
             stand, so that the point it returns is a countermodel of the
             problem's own clauses; a clause a question above has shown valid
             is skipped (the list is the one [per_clause] was built from, in
             the same order).  The guesses are satisfiability questions about
             quantifier-free relaxations and the proofs are validity questions
             asked like the sequence-instantiated ones, all under the array
             side's refutation budget; only a proof is read, so a wrong guess
             costs time and never an answer. *)
          let scalar_pin_refutation ~within ?expired ?search_complete
              ?(early = false) () =
            let applicable =
              early && (ZeroUnknownConfig.Switch.early_pins_require_applicable config.zero_unknown)
            in
            (* an early pin's per-question cap and whole budget ([within])
               also bound the last attempts [proved_at]'s validity proofs make
               after their forms (the external solver's retry and the lemma
               route), which otherwise run under their own process-wide
               budgets: on a Rust-derived bit-set input, seven such retries
               made the early point pin take 32-38 s against its 10 s.  The
               late pins keep them unbounded, as before *)
            (if early then SeqInstantiation.with_last_attempt_budget within
             else fun f -> f ())
            @@ fun () ->
            NoUnknownScalarPin.refute ~log:Debug.print ?expired ?search_complete
              ~skip_opaque:applicable
              ?infeasible:
                (if applicable then
                   Some
                     (fun psi ->
                       match within () with
                       | None -> false
                       | Some timeout -> (
                           let r =
                             Z3Smt.Z3interface.with_rlimit ~label:"ladder"
                               config.zero_unknown.budgets.query_rlimit
                             @@ fun () ->
                             Z3Smt.Z3interface.check_sat
                               ~timeout:(Some timeout) ~fresh_solver:true
                               ~id:None (fenv_used_by psi) [ psi ]
                           in
                           Debug.print
                           @@ lazy
                                (sprintf
                                   "[no-unknown verdict] point pin, \
                                    applicability precheck: %s"
                                   (match r with
                                   | `Sat _ -> "sat"
                                   | `Unsat -> "unsat (piece skipped)"
                                   | `Timeout -> "timeout"
                                   | `Unknown reason -> "unknown: " ^ reason));
                           match r with `Unsat -> true | _ -> false))
                 else None)
              ?residual_sat:
                (if (ZeroUnknownConfig.Switch.drop_valid_premises_before_pin config.zero_unknown) then
                   Some
                     (fun psi ->
                       match within () with
                       | None -> None
                       | Some timeout -> (
                           let r =
                             Z3Smt.Z3interface.with_rlimit
                               ~label:"ladder"
                               config.zero_unknown.budgets.query_rlimit
                             @@ fun () ->
                             Z3Smt.Z3interface.check_sat
                               ~timeout:(Some timeout) ~fresh_solver:true
                               ~id:None (fenv_used_by psi) [ psi ]
                           in
                           Debug.print
                           @@ lazy
                                (sprintf
                                   "[no-unknown verdict] unproved premises at \
                                    a point: %s"
                                   (match r with
                                   | `Sat _ -> "sat (a refutation)"
                                   | `Unsat -> "unsat (says nothing)"
                                   | `Timeout -> "timeout"
                                   | `Unknown reason -> "unknown: " ^ reason));
                           match r with `Sat model -> Some model | _ -> None))
                 else None)
              ~enabled:(ZeroUnknownConfig.Switch.pin_scalars config.zero_unknown)
              ~default_compound:(ZeroUnknownConfig.Switch.pin_scalars_default_compound_values config.zero_unknown)
              ~binder_free_relaxation:
                (ZeroUnknownConfig.Switch.pin_scalars_binder_free_relaxation config.zero_unknown)
              ~already_valid:(fun i ->
                i < Array.length clause_valid && clause_valid.(i))
              ~guess:(fun psi ->
                match within () with
                | None -> None
                | Some timeout ->
                let r =
                  Z3Smt.Z3interface.with_rlimit ~label:"ladder" config.zero_unknown.budgets.query_rlimit
                  @@ fun () ->
                  Z3Smt.Z3interface.check_sat
                    ~timeout:(Some timeout)
                    ~fresh_solver:true ~id:None (fenv_used_by psi) [ psi ]
                in
                Debug.print
                @@ lazy
                     (sprintf "[no-unknown verdict] point guess: %s"
                        (match r with
                        | `Sat _ -> "a point (not yet a refutation)"
                        | `Unsat -> "none"
                        | `Timeout -> "timeout"
                        | `Unknown reason -> "unknown: " ^ reason));
                match r with `Sat model -> Some model | _ -> None)
              ~ask:(fun c ->
                let c =
                  if config.zero_unknown.rewrites.onepoint.split then
                    Ast.Evaluator.elim_onepoint_and_split_binders c
                  else c
                in
                let r =
                  match within () with
                  | None -> `Timeout
                  | Some timeout -> ask_fresh_within timeout c
                in
                Debug.print
                @@ lazy
                     (sprintf "[no-unknown verdict] negation at a point: %s"
                        (match r with
                        | `Valid -> "valid"
                        | `Invalid _ -> "invalid (says nothing)"
                        | `Timeout -> "timeout"
                        | `Unknown reason -> reason
                        | `Sat _ | `Unsat -> "unexpected"));
                r)
              (Set.to_list @@ Ast.ClauseSetOld.to_formulas
              @@ Ast.ClauseSet.to_old_clause_set Map.Poly.empty
              @@ PCSP.Problem.clauses_of pcsp)
          in
          (* The relation pin (see [NoUnknownRelationPin]), tried after the
             point pin, on the clauses as they stand and skipping those shown
             valid, as the point pin does.  Its guesses are satisfiability
             questions about quantifier-free relaxations, of which only the
             sequence lengths are used; its pinned negations are asked like
             the sequence-pinned query, and only a model is read. *)
          (* the clauses this problem has open (not shown valid) that
             mention a relation, the one shape the relation pin acts on *)
          let open_relation_clause i c =
            (not (i < Array.length clause_valid && clause_valid.(i)))
            && NoUnknownRelationPin.mentions_relation c
          in
          (* the clauses the early relation pin reads after it has searched
             this problem's, when the preprocessing offered a problem
             ([NoUnknownLadder.early_pins_problem]): the second, unsplit
             preprocessing's clauses, none skipped (they are not this
             problem's, so none is shown valid).  Asked for only while an
             open clause mentions a relation, so that a problem whose relation
             clauses are all proved does not pay for the second
             preprocessing; the offered function remembers its answer *)
          let early_relation_pin_unsplit () =
            match !(NoUnknownLadder.early_pins_problem ()) with
            | None -> None
            | Some problem ->
                if
                  List.existsi ~f:open_relation_clause
                    (Set.to_list @@ Ast.ClauseSetOld.to_formulas
                    @@ Ast.ClauseSet.to_old_clause_set Map.Poly.empty
                    @@ PCSP.Problem.clauses_of pcsp)
                then
                  Option.map (problem ()) ~f:(fun p ->
                      ( Set.to_list @@ Ast.ClauseSetOld.to_formulas
                        @@ Ast.ClauseSet.to_old_clause_set Map.Poly.empty
                        @@ PCSP.Problem.clauses_of p,
                        fun _ -> false ))
                else None
          in
          (* [over]: the clauses searched and the indices among them to skip,
             in place of this problem's clauses and those shown valid *)
          let relation_pin_refutation ~within ?expired ?(early = false) ?over
              () =
            let clauses, shown_valid =
              match over with
              | Some over -> over
              | None ->
                  ( Set.to_list @@ Ast.ClauseSetOld.to_formulas
                    @@ Ast.ClauseSet.to_old_clause_set Map.Poly.empty
                    @@ PCSP.Problem.clauses_of pcsp,
                    fun i -> i < Array.length clause_valid && clause_valid.(i) )
            in
            (* one search of [refute] over [clauses], every question under
               [within], skipping the clauses [already_valid] names *)
            let search ~within ?expired ~already_valid () =
              let ask_sat what psi =
                match within () with
                | None -> None
                | Some timeout ->
                let r =
                  Z3Smt.Z3interface.with_rlimit ~label:"ladder" config.zero_unknown.budgets.query_rlimit
                  @@ fun () ->
                  Z3Smt.Z3interface.check_sat
                    ~timeout:(Some timeout)
                    ~fresh_solver:true ~id:None (fenv_used_by psi) [ psi ]
                in
                Debug.print
                @@ lazy
                     (sprintf "[no-unknown verdict] relation pin, %s: %s" what
                        (match r with
                        | `Sat _ -> "sat"
                        | `Unsat -> "unsat"
                        | `Timeout -> "timeout"
                        | `Unknown reason -> "unknown: " ^ reason));
                Some r
              in
              let sat what psi =
                match ask_sat what psi with Some (`Sat model) -> Some model | _ -> None
              in
              let infeasible =
                if early && (ZeroUnknownConfig.Switch.early_relation_pin_precheck config.zero_unknown)
                then
                  Some
                    (fun psi ->
                      match ask_sat "shape precheck" psi with
                      | Some `Unsat -> true
                      | _ -> false)
                else None
              in
              let applicable =
                early && (ZeroUnknownConfig.Switch.early_pins_require_applicable config.zero_unknown)
              in
              NoUnknownRelationPin.refute ~log:Debug.print ?expired ?infeasible
                ~by_length_vectors:
                  (early
                  && (ZeroUnknownConfig.Switch.early_relation_pin_length_shapes config.zero_unknown))
                ~skip_relation_free_clauses:applicable
                ?cheap_infeasible:
                  (if applicable then
                     Some
                       (fun psi ->
                         match ask_sat "applicability precheck" psi with
                         | Some `Unsat -> true
                         | _ -> false)
                   else None)
                ~attempts_per_piece:
                  config.zero_unknown.pins.relation_attempts_per_piece
                ~enabled:config.zero_unknown.pins.relations
                ~already_valid
                ~guess:(sat "shape guess")
                ~ask:(sat "pinned negation (sat is a refutation)")
                clauses
            in
            let gc_every =
              if early then
                (ZeroUnknownConfig.Switch.early_relation_pin_full_major_every config.zero_unknown)
              else None
            in
            (match gc_every with
            | Some n -> Z3Smt.Z3interface.with_new_context_full_major_every n
            | None -> fun f -> f ())
            @@ fun () ->
            if
              early
              && ZeroUnknownConfig.Switch.early_relation_pin_per_clause
                   config.zero_unknown
            then (
              (* [zero_unknown.early_stage.pins (Early_pins
                 relation.per_clause)]: one search per open clause that has a
                 Boolean-valued array among its free variables, in clause
                 order, the n-th of k given the whole budget's rest divided
                 by k - n + 1, from when it starts (what an earlier clause
                 left unspent passes on), every question also under the
                 enclosing [within], and [refute]'s cap on pinned negations
                 counted per clause.  Each search is [refute]'s on one clause,
                 so a model it returns is a countermodel as before; only how
                 the budget is spread over the clauses changes.  Why: the pin
                 spends its whole budget on the first open clause whose shape
                 guesses do not decide, and so never reaches a later clause it
                 refutes in under a second -- seen where a valid clause had
                 stayed open only because the quick sweep's sequence-axiom
                 question about it came out slow in that process. *)
              let whole_ms =
                match
                  ZeroUnknownConfig.Switch.early_relation_pin_budget
                    config.zero_unknown
                with
                | Some (_, whole) -> whole
                | None ->
                    snd
                      (ZeroUnknownConfig.Switch.early_pins_budget
                         config.zero_unknown)
              in
              let started = Common.Clock.now_s () in
              let left_ms () =
                whole_ms
                - Float.iround_down_exn
                    ((Common.Clock.now_s () -. started) *. 1000.)
              in
              let expired_now () =
                match expired with Some f -> f () | None -> false
              in
              let open_clauses =
                List.filter_mapi clauses ~f:(fun i c ->
                    if shown_valid i || not (NoUnknownRelationPin.mentions_relation c)
                    then None
                    else Some i)
              in
              let k = List.length open_clauses in
              List.find_mapi open_clauses ~f:(fun n i ->
                  let left = left_ms () in
                  if left <= 0 || expired_now () || Option.is_none (within ())
                  then None
                  else
                    let deadline =
                      Common.Clock.now_s ()
                      +. (Float.of_int (left / (k - n)) /. 1000.)
                    in
                    let within_clause () =
                      match within () with
                      | None -> None
                      | Some t ->
                          let l =
                            Float.iround_down_exn
                              ((deadline -. Common.Clock.now_s ()) *. 1000.)
                          in
                          if l <= 0 then None else Some (Int.min t l)
                    in
                    search ~within:within_clause
                      ~expired:(fun () ->
                        expired_now () || Option.is_none (within_clause ()))
                      ~already_valid:(fun j -> j <> i || shown_valid j)
                      ()))
            else (
              (* act census (instrument only): two or more clauses to share
                 the budget among is where [relation.per_clause] acts *)
              if
                early && Common.ActCensus.on ()
                && List.count (List.filteri clauses ~f:(fun i c ->
                       (not (shown_valid i))
                       && NoUnknownRelationPin.mentions_relation c)) ~f:(fun _ -> true)
                   >= 2
              then
                Common.ActCensus.note
                  "zero_unknown.early_stage.pins.relation.per_clause";
              search ~within ?expired ~already_valid:shown_valid ())
          in
          (* the early relation pin's search over the unsplit problem's
             clauses ([early_relation_pin_unsplit]) under [fresh ()], a budget
             of its own made when the search starts.  Asked with the
             unprefixed fresh names drawn in a replay scope of their own (not
             from the process-wide counter) and on contexts set aside from
             this domain's pools, so that the stages after this one draw the
             same names and meet the same pooled contexts as without it: a
             borderline later question (a sequence pin's) was seen to stop
             refuting once a second preprocessing here had moved the
             process-wide name counter and the pools.  Reads only a
             countermodel of a clause of the unsplit problem, which refutes
             the input (the split is an equivalence per clause) *)
          let unsplit_relation_refutation fresh =
            Ast.Ident.with_replayed_fresh_names
              ~scope:(NoUnknownLadder.early_unsplit_scope ())
            @@ fun () ->
            Z3Smt.Z3interface.with_isolated_pools @@ fun () ->
            match
              Common.PhaseTime.with_phase "unsplit" early_relation_pin_unsplit
            with
            | None -> None
            | Some over ->
                Common.PhaseTime.event_here "unsplit-for-early-pins";
                Common.ActCensus.note
                  "clauses.split_single_cons.outside_early_pins";
                let within, expired = fresh () in
                Common.PhaseTime.with_phase "unsplit-search" @@ fun () ->
                relation_pin_refutation ~within ?expired ~early:true ~over ()
          in
          (* [stage] prefixes the ladder phases the three pins are traced
             under: [""] for the late pins, ["early-"] for the early ones *)
          let pins ?expired ?relation_budget ?per_pin_budget ?fresh_budget
              ?(relation_first = false) ?(skip_point = false) ~stage ~within ()
              =
            let early = String.equal stage "early-" in
            (* [per_pin_budget]: a fresh [(within, expired)] made when each pin
               starts, in place of the shared ones, so that no pin spends
               another's budget *)
            let budget () =
              match per_pin_budget with
              | None -> (within, expired)
              | Some fresh -> fresh ()
            in
            let relpin () =
              enter_phase (stage ^ "relpin");
              (* [relation_budget]: the relation pin's own
                 [(within, expired)], in place of the shared ones *)
              let within, expired =
                match relation_budget with
                | None -> budget ()
                | Some (within, expired) -> (within, expired)
              in
              match relation_pin_refutation ~within ?expired ~early () with
              | Some _ as r -> r
              | None when early -> (
                  (* then the unsplit problem's clauses
                     ([unsplit_relation_refutation]), under a [fresh_budget]
                     of their own (the shared one has run during the first
                     search), after every question the first search asks, so
                     that a refutation found there is found as without them.
                     No [fresh_budget] is passed when that search is a stage
                     of its own after the exact forms
                     ([NoUnknownLadder.Unsplit_pins]) *)
                  match fresh_budget with
                  | None -> None
                  | Some fresh -> unsplit_relation_refutation fresh)
              | None -> None
            in
            let seqpin () =
              enter_phase (stage ^ "seqpin");
              let within, expired = budget () in
              seq_pin_refutation ~within ?expired ~early ()
            in
            let scalarpin () =
              enter_phase (stage ^ "scalarpin");
              let within, expired = budget () in
              scalar_pin_refutation ~within ?expired ~early ()
            in
            (* each pin reads only a model of a strengthened negation, so the
               order changes which is asked first under a shared budget,
               never an answer.  [skip_point]: the point pin is left out,
               having already searched every open clause before the exact
               forms ([NoUnknownLadder.point_pin_searched_all]) *)
            let scalarpin () = if skip_point then None else scalarpin () in
            (* A pin only guesses a strengthening of the negation and reads a
               model of it; it never proves anything.  So a pin that raises
               (a defect in building its question) is treated as one that
               found nothing: the next pin and the rest of the ladder run as
               without it, and the answer, if any, still comes from a question
               that was asked.  Without this a raise inside one guess ended
               the whole solve with no verdict.  Asynchronous exceptions (the
               timer's timeout, an interrupt, running out of memory or stack)
               are re-raised, so the budgets still end the ladder. *)
            let guarded name pin () =
              try pin ()
              with exn_ when not (Common.Timer.is_async exn_) ->
                Common.PhaseTime.event_here ~in_copy:false "pin-raised";
                Debug.print
                @@ lazy
                     (sprintf "[no-unknown verdict] %s pin raised %s: dropped"
                        name (Exn.to_string exn_));
                None
            in
            let relpin = guarded "relation" relpin
            and seqpin = guarded "sequence" seqpin
            and scalarpin = guarded "point" scalarpin in
            List.find_map
              (if relation_first then [ relpin; seqpin; scalarpin ]
               else [ seqpin; scalarpin; relpin ])
              ~f:(fun pin -> pin ())
          in
          (* whether a clause not yet shown valid has a Boolean-valued array
             among its free variables, the only shape the relation pin acts
             on *)
          let some_relation_clause () =
            List.existsi
              (Set.to_list @@ Ast.ClauseSetOld.to_formulas
              @@ Ast.ClauseSet.to_old_clause_set Map.Poly.empty
              @@ PCSP.Problem.clauses_of pcsp)
              ~f:(fun i c ->
                (not (i < Array.length clause_valid && clause_valid.(i)))
                && NoUnknownRelationPin.mentions_relation c)
          in
          let pin_refutation () =
            if not (NoUnknownLadder.late_pins_read !NoUnknownLadder.read) then (
              (* a refutation only, and the caller reads only a proof *)
              Common.PhaseTime.event_here "late-pins-not-read";
              None)
            else if !NoUnknownLadder.early_only then
              (* the caller asked for the early stages only *)
              None
            else
            pins ~stage:""
              ~within:(fun () -> Some config.zero_unknown.budgets.refutation_ms)
              ()
          in
          (* The same three pins asked once EARLY, right after the quick
             sweep and before the rewritten forms and the sequence
             instantiation, under [zero_unknown.early_stage.pins]'s
             [(per question, whole)] budget.  Moving them changes only when
             they are asked and with what budget, never an answer: a pin reads
             only a model of the negation pinned to a point, a length or a
             relation (a strengthening of the negation, so every such model is
             a countermodel of the problem) or a proof that the pinned negation
             is valid, and an undecided or unasked question is dropped.  A
             clause the quick sweep showed valid is skipped, as the late pins
             skip every clause shown valid.  When nothing is found here the
             ladder continues unchanged and the late pins still run with their
             full budget. *)
          (* The point pin asked alone, before the exact forms
             ([zero_unknown.early_stage.pins (Early_pins point_pin_first)],
             [NoUnknownLadder.Point_pin]), with a budget of its own: the early
             pins' [(per question, whole)] pair, its clock started at its
             first question ([NoUnknownLadder.lazy_budget]), so that no other
             pin can spend it.  It is the early point pin of [pins] with
             nothing else changed: the clauses as they stand, the quick
             sweep's proofs skipped, only a point at which the clause's
             negation is proved read.  When it searched every open clause
             under full per-question caps
             ([NoUnknownLadder.point_pin_searched_all]),
             [early_point_pin_searched_all] makes the later early pins leave
             the point pin out. *)
          let early_point_pin_searched_all = ref false in
          let early_point_pin_refutation () =
            enter_phase "early-pointpin";
            let per_query, whole = (ZeroUnknownConfig.Switch.early_pins_budget config.zero_unknown) in
            let within, expired =
              NoUnknownLadder.lazy_budget ~now:Common.Clock.now_s
                (per_query, whole)
            in
            let expired =
              if (ZeroUnknownConfig.Switch.early_pins_stop_at_deadline config.zero_unknown) then
                Some expired
              else None
            in
            let search_complete = ref false in
            let r =
              (match (ZeroUnknownConfig.Switch.early_pins_full_major_every config.zero_unknown) with
              | Some n -> Z3Smt.Z3interface.with_new_context_full_major_every n
              | None -> fun f -> f ())
              @@ fun () ->
              scalar_pin_refutation ~within ?expired ~search_complete
                ~early:true ()
            in
            early_point_pin_searched_all :=
              Option.is_none r
              && NoUnknownLadder.point_pin_searched_all
                   ~search_complete:!search_complete ~next_budget:(within ())
                   ~per_query;
            Debug.print
            @@ lazy
                 (sprintf "[no-unknown verdict] early point pin first: %s"
                    (match r with
                    | Some _ -> "a refutation"
                    | None when !early_point_pin_searched_all ->
                        "nothing, every open clause searched"
                    | None -> "nothing, search cut short"));
            r
          in
          (* [per_pin]: each early pin gets the whole of
             [zero_unknown.early_stage.pins (Early_pins budget)] from when it starts, rather
             than all three sharing one from when the first starts.  Used by
             the raced copy of [zero_unknown.early_stage.pins (Early_pins raced)], which runs
             beside the process: the shared budget exists to bound how long the
             pins delay the ladder, and a copy delays nothing.  Why: with every
             clause still open (before the exact forms prove any), the
             sequence-length pin's questions on a Rust-derived bit-set input
             reached their 1 s caps on four clauses and spent the shared 10 s,
             leaving the point pin, the one that refutes it, about two. *)
          (* a fresh copy of the early pins' [(per question, whole)]
             budget, its clock started now *)
          let early_fresh_budget () =
            let per_query, whole =
              ZeroUnknownConfig.Switch.early_pins_budget config.zero_unknown
            in
            let deadline =
              Common.Clock.now_s () +. (Float.of_int whole /. 1000.)
            in
            let within () =
              let left =
                Float.iround_down_exn
                  ((deadline -. Common.Clock.now_s ()) *. 1000.)
              in
              if left <= 0 then None else Some (Int.min per_query left)
            in
            let expired =
              if
                ZeroUnknownConfig.Switch.early_pins_stop_at_deadline
                  config.zero_unknown
              then Some (fun () -> Option.is_none (within ()))
              else None
            in
            (within, expired)
          in
          (* whether the unsplit search is the stage of its own
             [NoUnknownLadder.Unsplit_pins] after the exact forms rather than
             the tail of the early relation pin *)
          let unsplit_last =
            ZeroUnknownConfig.Switch.early_pins config.zero_unknown
            && ZeroUnknownConfig.Switch.early_unsplit_after_exact_forms
                 config.zero_unknown
          in
          let early_pin_refutation ?(per_pin = false) () =
            match (ZeroUnknownConfig.Switch.early_pins config.zero_unknown) with
            | false -> None
            | true ->
                let fresh_budget = early_fresh_budget in
                let within, expired = fresh_budget () in
                let per_pin_budget =
                  if per_pin then Some fresh_budget else None
                in
                let relation_budget =
                  Option.map (ZeroUnknownConfig.Switch.early_relation_pin_budget config.zero_unknown)
                    ~f:(fun budget ->
                      let within, expired =
                        if (ZeroUnknownConfig.Switch.early_relation_pin_cpu_clock config.zero_unknown)
                        then
                          NoUnknownLadder.cpu_budget ~now:Common.Clock.now_s
                            ~cpu:NoUnknownLadder.thread_cpu_seconds
                            ~max_scale:
                              (ZeroUnknownConfig.Switch.early_relation_pin_max_scale config.zero_unknown)
                            budget
                        else
                          NoUnknownLadder.lazy_budget
                            ~now:Common.Clock.now_s budget
                      in
                      ( within,
                        if (ZeroUnknownConfig.Switch.early_pins_stop_at_deadline config.zero_unknown)
                        then Some expired
                        else None ))
                in
                let relation_first =
                  (ZeroUnknownConfig.Switch.early_relation_pin_first config.zero_unknown)
                  && some_relation_clause ()
                in
                let r =
                  (match (ZeroUnknownConfig.Switch.early_pins_full_major_every config.zero_unknown) with
                  | Some n ->
                      Z3Smt.Z3interface.with_new_context_full_major_every n
                  | None -> fun f -> f ())
                  @@ fun () ->
                  pins ?expired ?relation_budget ?per_pin_budget
                    ?fresh_budget:
                      (if unsplit_last then None else Some fresh_budget)
                    ~relation_first
                    ~skip_point:!early_point_pin_searched_all ~stage:"early-"
                    ~within ()
                in
                Debug.print
                @@ lazy
                     (sprintf "[no-unknown verdict] early pins: %s"
                        (if Option.is_some r then "a refutation"
                         else "nothing"));
                r
          in
          (* The cheap pin question ([zero_unknown.early_stage.pins (Early_pins cheap_first)],
             [SeqPin.cheap_first]), asked before the exact forms when the
             shape says it is cheap.  Like the sequence-length pin it is given
             the clauses as they stand (a countermodel of a rewritten clause
             need not be one of the original), leaves out those shown valid,
             and reads only a model of a strengthened negation.  One question,
             under the early pins' per-question cap. *)
          let cheap_pin_refutation () =
            enter_phase "early-cheappin";
            let open_ =
              List.filteri
                (Set.to_list @@ Ast.ClauseSetOld.to_formulas
                @@ Ast.ClauseSet.to_old_clause_set Map.Poly.empty
                @@ PCSP.Problem.clauses_of pcsp)
                ~f:(fun i _ ->
                  not (i < Array.length clause_valid && clause_valid.(i)))
            in
            match NoUnknownSeqPin.cheap_first open_ with
            | `Not_applicable ->
                Debug.print
                @@ lazy
                     "[no-unknown verdict] cheap pin first: not applicable \
                      (no open clause keeps a free sequence at length 0)";
                None
            | `Too_large n ->
                Debug.print
                @@ lazy
                     (sprintf
                        "[no-unknown verdict] cheap pin first: not asked, %d \
                         nodes > %d"
                        n NoUnknownSeqPin.cheap_max_size);
                None
            | `Ask psi -> (
                let per_query, _ = (ZeroUnknownConfig.Switch.early_pins_budget config.zero_unknown) in
                let r =
                  Z3Smt.Z3interface.with_rlimit ~label:"ladder"
                    config.zero_unknown.budgets.query_rlimit
                  @@ fun () ->
                  Z3Smt.Z3interface.check_sat ~timeout:(Some per_query)
                    ~fresh_solver:true ~id:None (fenv_used_by psi) [ psi ]
                in
                Debug.print
                @@ lazy
                     (sprintf
                        "[no-unknown verdict] cheap pin first (length 0): %s"
                        (match r with
                        | `Sat _ -> "sat (a refutation)"
                        | `Unsat -> "unsat (says nothing)"
                        | `Timeout -> "timeout"
                        | `Unknown reason -> "unknown: " ^ reason));
                match r with `Sat model -> Some model | _ -> None)
          in
          (* the race of [zero_unknown.early_stage.pins (Early_pins raced)], when started:
             finished (its copy killed, or the process parked when the copy
             has already taken the run over) before the verdict leaves *)
          let pins_race = ref None in
          (* the last sequence instantiation, a proof only: not run when the
             caller reads only a refutation *)
          let late_seq_instantiation undecided =
            if
              NoUnknownLadder.seq_instantiation_read !NoUnknownLadder.read
            then (
              enter_phase "late-seqinst";
              seq_instantiation undecided)
            else (
              Common.PhaseTime.event_here "late-seqinst-not-read";
              undecided)
          in
          let verdict =
            Exn.protect
              ~finally:(fun () ->
                Option.iter !pins_race ~f:PCSatCommon.ParallelRace.finish;
                pins_race := None)
              ~f:(fun () ->
            match
              (* every clause already proved (by the congruence match or the
                 shape proof, both of which read only proofs): nothing is
                 left to ask *)
              if
                config.zero_unknown.congruence_match
                && Array.for_all clause_valid ~f:Fn.id
              then None
              else
              match pieces_first () with
              | Some verdict -> Some verdict
              | None -> quick_sweep ()
            with
            | Some verdict -> verdict
            | None when Array.for_all clause_valid ~f:Fn.id -> `Valid
            | None ->
            (* the two early stages, in the order
               [zero_unknown.early_stage.pins_after_exact_forms] gives; either
               decides alone, so the order changes only when an answer is
               reached.  [conj_ask] below is the budget of the whole-conjunction
               questions, shortened under
               [zero_unknown.budgets.conjunction_ms_after_early] once the exact forms
               have run and left the problem undecided. *)
            let early_ran = config.zero_unknown.early_stage.exact_forms_first in
            let conj_ask ask_within phi =
              NoUnknownLadder.ask_conj
                ~timeout:
                  (NoUnknownLadder.conj_timeout
                     ~cap:config.zero_unknown.budgets.conjunction_ms_after_early
                     ~early_ran ~default:config.zero_unknown.budgets.query_ms)
                ~ask:ask_within phi
            in
            match
              NoUnknownLadder.first_decided
                (List.filter
                   ~f:(fun stage ->
                     let r =
                       NoUnknownLadder.stage_read !NoUnknownLadder.read stage
                     in
                     if not r then
                       Common.PhaseTime.event_here "early-pins-not-read";
                     r)
                @@ NoUnknownLadder.early_order
                   ~cheap_pins_first:
                     ((ZeroUnknownConfig.Switch.early_cheap_pins_first config.zero_unknown)
                     && (ZeroUnknownConfig.Switch.early_pins config.zero_unknown)
                     && (ZeroUnknownConfig.Switch.pin_seq_lengths config.zero_unknown))
                   ~pins_raced:
                     ((ZeroUnknownConfig.Switch.early_pins_raced config.zero_unknown)
                     && (ZeroUnknownConfig.Switch.early_pins config.zero_unknown))
                   ~point_pin_first:
                     ((ZeroUnknownConfig.Switch.early_point_pin_first config.zero_unknown)
                     && (ZeroUnknownConfig.Switch.early_pins config.zero_unknown)
                     && (ZeroUnknownConfig.Switch.pin_scalars config.zero_unknown))
                   ~unsplit_last
                   ~pins_after_exact:
                     config.zero_unknown.early_stage.pins_after_exact_forms
                   ())
                ~run:(function
                  | NoUnknownLadder.Raced_pins -> (
                      if PCSatCommon.SolveDeadline.active () then None
                      else
                        match
                          Common.PhaseTime.with_phase "early-pins-fork"
                            (fun () ->
                              PCSatCommon.ParallelRace.start
                                ~report:(fun () ->
                                  Common.PhaseTime.report
                                    ~reason:"early-pins-copy-answered")
                                ~log:(fun msg ->
                                  if !Common.PhaseTime.on
                                     || !Common.PhaseTime.in_child
                                  then (
                                    prerr_endline
                                      (sprintf
                                         "phase-time-race: at=%.3f \
                                          early-pins: %s"
                                         (Common.PhaseTime.now ()
                                         -. Common.PhaseTime.t0)
                                         msg);
                                    Out_channel.flush stderr))
                                (fun () ->
                                  (* with COAR_RACE_STATS set, the copy's own
                                     cost of the pins on stderr: wall and CPU
                                     seconds, collections and the heap.  An
                                     instrument: it decides nothing *)
                                  let stats =
                                    Option.is_some
                                      (Stdlib.Sys.getenv_opt "COAR_RACE_STATS")
                                  in
                                  let t0 = Common.Clock.now_s ()
                                  and c0 = Core_unix.times ()
                                  and g0 = Stdlib.Gc.quick_stat () in
                                  let r = early_pin_refutation ~per_pin:true () in
                                  (if stats then
                                     let c1 = Core_unix.times ()
                                     and g1 = Stdlib.Gc.quick_stat () in
                                     prerr_endline
                                       (sprintf
                                          "race-stats: pins wall=%.3f user=%.3f \
                                           sys=%.3f minor=%d major=%d \
                                           heap_words=%d top_heap_words=%d \
                                           found=%b"
                                          (Common.Clock.now_s () -. t0)
                                          (c1.tms_utime -. c0.tms_utime)
                                          (c1.tms_stime -. c0.tms_stime)
                                          (g1.minor_collections
                                         - g0.minor_collections)
                                          (g1.major_collections
                                         - g0.major_collections)
                                          g1.heap_words g1.top_heap_words
                                          (Option.is_some r)));
                                  r))
                        with
                        | `Won model ->
                            (* this is the copy, which now is the run *)
                            Some (`Invalid model)
                        | `Racing t ->
                            pins_race := Some t;
                            None
                        | `Not_started -> None)
                  | NoUnknownLadder.Cheap_pins ->
                      Option.map (cheap_pin_refutation ()) ~f:(fun model ->
                          `Invalid model)
                  | NoUnknownLadder.Point_pin ->
                      (* counted so that a run shows the early point pin was
                         asked ahead of the exact forms; changes nothing *)
                      Common.PhaseTime.event_here "point-pin-first";
                      Option.map (early_point_pin_refutation ())
                        ~f:(fun model -> `Invalid model)
                  | NoUnknownLadder.Early_pins ->
                      Option.map (early_pin_refutation ()) ~f:(fun model ->
                          `Invalid model)
                  | NoUnknownLadder.Exact_forms -> exact_forms_first ()
                  | NoUnknownLadder.Unsplit_pins ->
                      (* the unsplit search after every other early stage
                         ([zero_unknown.early_stage.pins (Early_pins
                         relation.unsplit_after_exact_forms)]), on the
                         relation clauses still open, under a fresh copy of
                         the early pins' budget *)
                      enter_phase "early-unsplit";
                      (match
                         ZeroUnknownConfig.Switch.early_pins_full_major_every
                           config.zero_unknown
                       with
                      | Some n ->
                          Z3Smt.Z3interface.with_new_context_full_major_every n
                      | None -> fun f -> f ())
                      @@ fun () ->
                      Option.map
                        (unsplit_relation_refutation early_fresh_budget)
                        ~f:(fun model -> `Invalid model))
            with
            | Some verdict -> verdict
            | None when Array.for_all clause_valid ~f:Fn.id -> `Valid
            | None when !NoUnknownLadder.early_only ->
                (* the caller asked for the early stages only (see
                   [NoUnknownLadder.early_only]): undecided, and the late pins
                   are not run either *)
                Common.PhaseTime.event_here "ladder-early-only-stop";
                `Timeout
            | None -> (
            (* Ask the conjunction first -- that is the question, and it is what
               a solver is best at -- and only where it does not settle, ask the
               clauses ONE AT A TIME.  A conjunction is valid exactly when every
               conjunct is, so a clause answered `Invalid` refutes the whole,
               and every clause answered `Valid` -- in this pass or in the
               rewritten one below -- proves it.
               Splitting UNCONDITIONALLY would be the wrong shape: the two are
               equivalent as questions and not as queries, so a solver can prove
               the conjunction while failing on one conjunct, and a split-always
               version can lose an answer this one keeps.
               What it buys: one constraint that does not settle -- an
               existential over an array standing for a sequence's history,
               which Z3 answers "unknown (incomplete (theory array))" on --
               used to hide the refutation another clause carried, so a problem
               whose answer is decided came back `unknown`.  The same holds the
               other way round: the Thrust call-site queries have residual
               clauses each decided `Valid` in milliseconds whose conjunction
               spends the whole budget, and while the split looked only for a
               refutation those answers were dropped and the problem came back
               `timeout`. *)
            enter_phase "conj";
            match conj_ask conj_within asked with
            | (`Valid | `Invalid _) as verdict -> verdict
            | undecided -> (
                enter_phase "conj-opened";
                match conj_ask conj_within (open_single_cons_binders asked) with
                | (`Valid | `Invalid _) as verdict -> verdict
                | _ -> (
                (* stops at the first refutation, as before; a clause shown
                   valid is recorded, and every clause valid is the proof *)
                let all_valid () = Array.for_all clause_valid ~f:Fn.id in
                enter_phase "pooled";
                match
                  List.find_mapi per_clause ~f:(fun i c ->
                      if clause_valid.(i) then None
                      else
                      match ask_clause_by_pieces ~what:"pooled" ~ask c with
                      | `Invalid model -> Some (`Invalid model)
                      | `Valid ->
                          mark_valid i;
                          None
                      | _ -> None)
                with
                | Some verdict -> verdict
                | None when all_valid () -> `Valid
                | None -> (
                    match per_clause_rewritten with
                    | None -> late_seq_instantiation undecided
                    | Some rewritten -> (
                        (* a clause already shown valid need not be asked
                           again: it has no countermodel to offer, and the
                           conjunction is proved once the others are *)
                        let open_ =
                          List.filter_mapi rewritten ~f:(fun i c ->
                              if clause_valid.(i) then None
                              else Some (i, if remember then left_of i c else c))
                        in
                        enter_phase "rewritten-conj";
                        match
                          conj_ask ask_fresh_within
                            (Ast.LogicOld.Formula.and_of (List.map ~f:snd open_))
                        with
                        | (`Valid | `Invalid _) as verdict -> verdict
                        | _ -> (
                            enter_phase "rewritten";
                            match
                              List.find_map open_ ~f:(fun (i, c) ->
                                  let r =
                                    ask_rewritten_clause
                                      ?unproved:(unproved_of i)
                                      ~what:"rewritten" ~ask:ask_fresh c
                                  in
                                  (match r with
                                  | `Valid -> mark_valid i
                                  | _ -> ());
                                  Debug.print
                                  @@ lazy
                                       (sprintf
                                          "[no-unknown verdict] rewritten \
                                           clause %s: size %d: %s"
                                          (match r with
                                          | `Valid -> "valid"
                                          | `Invalid _ -> "invalid"
                                          | `Timeout -> "timeout"
                                          | `Unknown reason -> reason
                                          | `Sat _ | `Unsat -> "unexpected")
                                          (Ast.LogicOld.Formula.ast_size c)
                                          (Ast.LogicOld.Formula.str_of_prefix
                                             c));
                                  match r with
                                  | `Invalid model -> Some (`Invalid model)
                                  | _ -> None)
                            with
                            | Some verdict -> verdict
                            | None when all_valid () -> `Valid
                            | None -> late_seq_instantiation undecided)))))))
          in
          (* With COAR_COUNT_LADDER_CLAUSES set in the environment, how many
             of the clauses this ladder was asked about it showed valid, as
             one phase-report event [ladder-clauses-valid:K-of-N].  An
             instrument: it decides nothing. *)
          if count_clauses then
            Common.PhaseTime.event_here
              (sprintf "ladder-clauses-valid:%d-of-%d"
                 (Array.count clause_valid ~f:Fn.id)
                 (Array.length clause_valid));
          (* The run is about to end undecided.  Say whether a budget is the
             reason -- a question cut by it, as against a solver that answered
             "unknown" -- in the trace always and, under
             [zero_unknown.budgets.report_exhaustion], on stderr; the result is whether that
             option turns a [timeout] into [unknown]. *)
          let budget_exhausted () =
            if !budget_cut = 0 then false
            else begin
              let msg =
                sprintf
                  "budget exhausted: %d of %d validity queries of the \
                   zero-unknown verdict ran out of their budget (%d ms wall \
                   clock each%s; coordinator fields zero_unknown.budgets.query_ms, \
                   zero_unknown.budgets.query_rlimit)"
                  !budget_cut !budget_asked config.zero_unknown.budgets.query_ms
                  (match config.zero_unknown.budgets.query_rlimit with
                  | None -> ""
                  | Some r -> sprintf ", rlimit %d" r)
              in
              Debug.print @@ lazy ("[no-unknown verdict] " ^ msg);
              (* opted into: the person who set the option asked for the
                 reason, and a reason behind a tracing flag is one they do
                 not have *)
              if config.zero_unknown.budgets.report_exhaustion then prerr_endline msg;
              config.zero_unknown.budgets.report_exhaustion
            end
          in
          (* The countermodel is recorded with witness terms for the
             refuted clause's universal binders when a certificate is asked
             for (see [CountermodelWitness]); finding them costs solver
             questions, so nothing is computed otherwise, and even then only
             a suspension is built here: the search runs when a printer or a
             checker reads the terms, after the verdict ([lazy_witnesses]). *)
          let countermodel_witness model =
            if WitnessConfig.records_unsat witness then
              Some
                (UnsatWitness.make ~problem:(Some pcsp) senv
                   (UnsatWitness.Countermodel
                      {
                        formula = phi;
                        model;
                        witnesses =
                          lazy_witnesses
                            ~timeout:(Some config.zero_unknown.budgets.query_ms) phi
                            model;
                      }))
            else None
          in
          let refuted_by model =
            let model =
              Ast.LogicOld.Formula.and_of
              @@ List.filter_map model ~f:(fun ((x, sort), t) ->
                  Option.map t ~f:(fun t ->
                      Ast.LogicOld.Formula.eq (Ast.LogicOld.Term.mk_var x sort) t))
            in
            let unsat_witness =
              countermodel_witness model
            in
            Ok
              ( PCSP.Problem.Unsat (Option.map unsat_witness ~f:payload_of),
                { iters with unsat_witness; kind_certificates = Map.Poly.empty }
              )
          in
          (* one answer-neutral event per refutation, named by the ladder
             stage that found it, so a phase report tells which stage a
             refuting caller (the lower-bound probe) needs *)
          (match verdict with
          | `Invalid _ ->
              Common.PhaseTime.event_here ("ladder-refuted-at:" ^ !ladder_phase)
          | _ -> ());
          match verdict with
          | `Valid -> Ok (PCSP.Problem.Sat Map.Poly.empty, iters)
          | `Invalid model ->
              let model =
                Ast.LogicOld.Formula.and_of
                @@ List.filter_map model ~f:(fun ((x, sort), t) ->
                    Option.map t ~f:(fun t ->
                        Ast.LogicOld.Formula.eq
                          (Ast.LogicOld.Term.mk_var x sort)
                          t))
              in
              let unsat_witness =
                countermodel_witness model
              in
              Ok
                ( PCSP.Problem.Unsat (Option.map unsat_witness ~f:payload_of),
                  {
                    iters with
                    unsat_witness;
                    kind_certificates = Map.Poly.empty;
                  } )
          | `Timeout -> (
              match pin_refutation () with
              | None ->
                  if budget_exhausted () then Ok (PCSP.Problem.Unknown, iters)
                  else Ok (PCSP.Problem.Timeout, iters)
              | Some model ->
                  Common.PhaseTime.event_here
                    ("ladder-refuted-at:" ^ !ladder_phase);
                  refuted_by model)
          | `Unknown _ -> (
              (* The validity question was not decided, which on these inputs
                 means the constraint contains an array literal: a solver asked
                 about one answers "incomplete (theory array)" and settles
                 nothing, however ground the rest of the goal is.

                 A refutation is a model of the NEGATED constraint, and adding
                 constraints to that negation only removes models -- so a
                 satisfiable strengthening of it is still a refutation, while an
                 unsatisfiable one says nothing and is simply dropped.  Fixing
                 the terms that bound an array literal's index makes its range
                 concrete, which is what takes the goal back inside the fragment
                 the solver decides.  Only the values 0, 1 and 2 are tried, and
                 only here, where the answer is otherwise already lost: the
                 whole search is three bounded queries on a path that was about
                 to return "unknown", so it cannot cost an answer.  The budget
                 is explicit because a quantified Z3 query is not interruptible
                 by this process's own timer. *)
              let bounds =
                (* a bound that mentions a variable bound inside the constraint
                   cannot be pinned from outside it, and naming one there would
                   be a different variable *)
                let free = Ast.LogicOld.Formula.tvs_of phi in
                Set.filter (Ast.Evaluator.array_literal_range_bounds phi)
                  ~f:(fun b ->
                    Set.is_subset (Ast.LogicOld.Term.tvs_of b) ~of_:free)
              in
              enter_phase "arraybound-pin";
              let refutation =
                if
                  Set.is_empty bounds
                  || not (NoUnknownLadder.late_pins_read !NoUnknownLadder.read)
                then None
                else
                  List.find_map [ 0; 1; 2 ] ~f:(fun v ->
                      let pins =
                        List.map (Set.to_list bounds) ~f:(fun b ->
                            Ast.LogicOld.Formula.eq b
                            @@ Ast.LogicOld.T_int.mk_int (Z.of_int v))
                      in
                      match
                        Z3Smt.Z3interface.with_rlimit
                          ~label:"ladder"
                          config.zero_unknown.budgets.query_rlimit
                        @@ fun () ->
                        Z3Smt.Z3interface.check_sat
                          ~timeout:(Some config.zero_unknown.budgets.refutation_ms)
                          ~id:None (Ast.LogicOld.get_fenv ())
                          (Ast.LogicOld.Formula.negate phi :: pins)
                      with
                      | `Sat model -> Some model
                      | _ -> None)
              in
              match
                match refutation with
                | None -> pin_refutation ()
                | some -> some
              with
              | None ->
                  ignore (budget_exhausted () : bool);
                  Ok (PCSP.Problem.Unknown, iters)
              | Some model ->
                  Common.PhaseTime.event_here
                    ("ladder-refuted-at:" ^ !ladder_phase);
                  let model =
                    Ast.LogicOld.Formula.and_of
                    @@ List.filter_map model ~f:(fun ((x, sort), t) ->
                        Option.map t ~f:(fun t ->
                            Ast.LogicOld.Formula.eq
                              (Ast.LogicOld.Term.mk_var x sort)
                              t))
                  in
                  let unsat_witness =
                    countermodel_witness model
                  in
                  Ok
                    ( PCSP.Problem.Unsat (Option.map unsat_witness ~f:payload_of),
                      {
                        iters with
                        unsat_witness;
                        kind_certificates = Map.Poly.empty;
                      } ))
          | `Sat _ | `Unsat ->
              assert false (* folded into Valid/Invalid above *)
        else
          match sweep_unknown_free ~witness pcsp with
          | Some result -> result
          | None -> (
          try
            let sol_eliminated, pcsp = eliminate_fn_preds pcsp in
            let open Or_error in
            last_version_space := None;
            let version =
              match MContext.context.version with
              | None -> Context.create_version pcsp
              | Some _ -> Context.significant_version_of MContext.context pcsp
            in
            Context.set_version MContext.context version;
            (* One spelling per example, always.  The labeler's unit
               propagation hands every example back in [ExClause.normalize]
               form, so an example a producer stored unnormalised (a resolvent
               guarded by [0 = 0], an argument [-5 + x]) would otherwise come
               back as a second value: the example sets, keyed on the value,
               would hold the same fact twice, as two truth-table rows and two
               labeling variables nothing ties together (342 examples for 279
               distinct facts were measured on one input).  That is duplicated
               work and never a gain, so the identification is not optional. *)
            Ast.ClauseGraph.set_dedup_normalized version.graph true;
            let new_state =
              VersionSpace.init ~witness oracle
              |> VersionSpace.set_fenv (PCSP.Problem.fenv_of pcsp)
              |> VersionSpace.set_examples version.graph
              |> VersionSpace.set_truth_table version.truth_table
              |> State.of_version_space
            in
            let messenger = PCSP.Problem.messenger_of pcsp in
            id := PCSP.Problem.id_of pcsp;
            if config.verbose then
              Context.show_graph ~pre:"init_" ~id:!id MContext.context.version;
            Debug.set_id !id;
            ExtFile.unwrap Cfg.config.rl_config >>= fun rl_config ->
            Common.PhaseTime.with_phase "cegis-init" (fun () ->
                (* each phase's build and the synthesizer's initialisation
                   start at a safe point to end a probe whose strict deadline
                   has passed ([SolveDeadline.check_at_stage]) *)
                config.phase_list
                |> List.map ~f:(fun phase ->
                    SolveDeadline.check_at_stage ();
                    build_phase pcsp rl_config phase)
                |> Result.all
                >>| fun phase_list ->
                List.iter phase_list ~f:(function
                  | US (module MUS) ->
                      SolveDeadline.check_at_stage ();
                      Common.PhaseTime.with_phase "init-S" MUS.init
                  | _ -> ());
                phase_list)
            >>= fun phase_list ->
            if rl_config.enable then (
              RLConfig.lock ();
              if rl_config.show_constraints then
                Debug.print_stdout
                @@ lazy
                     (sprintf "constraints: %s" @@ Yojson.Safe.to_string
                     @@ PCSP.Problem.to_yojson pcsp);
              if rl_config.show_num_constrs then
                Debug.print_stdout
                @@ lazy (sprintf "#constrs: %d" @@ PCSP.Problem.num_constrs pcsp);
              if rl_config.show_num_pvars then
                Debug.print_stdout
                @@ lazy (sprintf "#pvars: %d" @@ PCSP.Problem.num_pvars pcsp);
              if rl_config.show_dep_graph then
                Debug.print_stdout
                @@ lazy
                     (sprintf "dependency graph:\n%s\n"
                     @@ PCSP.Problem.str_of_graph
                     @@ PCSP.Problem.dep_graph_of_chc pcsp);
              RLConfig.unlock ());
            (* A validation phase may ask for a round of its own before the
               first synthesis (the Houdini-style pre-pass over declared
               candidate atoms).  Its result stands in for that validation
               phase's output in the first iteration, and only the phases after
               it run on it: an answer passes through them unchanged, and
               examples it adds are labelled and resolved as a validation's
               counterexamples are before the next synthesis sees them.  When
               it asks for nothing, the first iteration is the ordinary one.
               A lazy pre-pass ([houdini.schedule.after_ms]) is asked the same way
               at the start of each later iteration, with the wall-clock time
               since this loop started; it stands in for that iteration's
               phases up to and including the validation, and runs at most
               once. *)
            let loop_started = Common.Clock.now_ns () in
            let race = ref None in
            (* after a raced copy was given the right to answer -- this
               loop's pre-pass copy or a probe raced before the loop -- the loop
               stops at its next phase rather than compete with the copy *)
            let park_if_lost () =
              PCSatCommon.ParallelRace.park_if_handed ();
              Option.iter !race ~f:PCSatCommon.ParallelRace.park_if_lost
            in
            let pre_round iter e =
              match
                List.find_mapi phase_list ~f:(fun i -> function
                  | SU (module V : MSU) ->
                      Some
                        ( i,
                          if iter = 0 then V.houdini_before_synthesis
                          else
                            V.houdini_at_round_boundary
                              ~elapsed_s:
                                (Time_ns.Span.to_sec
                                   (Time_ns.diff (Common.Clock.now_ns ()) loop_started))
                        )
                  | _ -> None)
              with
              | None -> None
              | Some (i, prepass) ->
                  (if iter = 0 then
                     match List.nth_exn phase_list i with
                     | SU (module V : MSU) when V.houdini_seq_instantiation ->
                         ignore (set_onepoint_rewrite_switches () : bool * bool);
                         set_seq_instantiation_switches ()
                     | _ -> ());
                  let parallel =
                    if iter <> 0 then None
                    else
                      match List.nth_exn phase_list i with
                      | SU (module V : MSU) when V.houdini_in_parallel ->
                          Some V.houdini_parallel_prepass
                      | _ -> None
                  in
                  match parallel with
                  | Some _ when PCSatCommon.SolveDeadline.active () ->
                      (* the pre-pass is not run inside a nested solve bounded
                         by a deadline, in parallel or not *)
                      None
                  | Some prepass -> (
                      (* [houdini.schedule = Parallel _]: the copy that finds a solution
                         returns it here as the sequential pre-pass would and
                         runs the rest of the program; the process goes on as
                         if the pre-pass had found nothing *)
                      match
                        Common.PhaseTime.with_phase "houdini-parallel-fork"
                          (fun () ->
                            PCSatCommon.ParallelRace.start
                              ~final:(function
                                | State.Continue _ -> false
                                | _ -> true)
                              ~report:(fun () ->
                                Common.PhaseTime.report
                                  ~reason:"houdini-parallel-copy-answered")
                              ~log:(fun msg ->
                                (* a line of the phase account, so only when
                                   it is on (in the copy, where the account is
                                   off, when it was on in the process) *)
                                if !Common.PhaseTime.on || !Common.PhaseTime.in_child
                                then (
                                  prerr_endline
                                    (sprintf "phase-time-race: at=%.3f %s"
                                       (Common.PhaseTime.now ()
                                       -. Common.PhaseTime.t0)
                                       msg);
                                  Out_channel.flush stderr))
                              (fun () -> prepass e))
                      with
                      | `Won e' -> Some (i, e')
                      | `Racing t ->
                          race := Some t;
                          None
                      | `Not_started ->
                          Option.map
                            (Common.PhaseTime.with_phase "houdini" (fun () ->
                                 prepass e))
                            ~f:(fun e' -> (i, e')))
                  | None ->
                  Option.map
                    (Common.PhaseTime.with_phase "houdini" (fun () -> prepass e))
                    ~f:(fun e' -> (i, e'))
            in
            Exn.protect
              ~finally:(fun () ->
                (* the loop has its answer (or raised): the raced copy is
                   killed before the answer leaves, and if the copy has
                   already been given the right to answer this never returns *)
                Option.iter !race ~f:PCSatCommon.ParallelRace.finish;
                race := None)
              ~f:(fun () ->
            main_loop ~pcsp sol_eliminated messenger
              (fun iter e ->
                match pre_round iter e with
                | Some (i, e') ->
                    List.foldi (List.drop phase_list (i + 1)) ~init:(Ok (U e'))
                      ~f:(fun j acc p ->
                        park_if_lost ();
                        app_phase messenger pcsp iter (i + 1 + j) acc p)
                | None ->
                    List.foldi phase_list ~init:(Ok (U e)) ~f:(fun j acc p ->
                        park_if_lost ();
                        app_phase messenger pcsp iter j acc p))
              0 (Ok new_state))
          with NoSolution reason ->
            let unsat_witness =
              if_witness
                (UnsatWitness.make ~problem:(Some pcsp) senv
                   (UnsatWitness.External reason))
            in
            Ok
              ( PCSP.Problem.Unsat (Option.map unsat_witness ~f:payload_of),
                {
                  State.num_cegis_iters = 0;
                  unsat_witness;
                  kind_certificates = Map.Poly.empty;
                } )))

  (* [unknown_free_clauses.sweep]: see [UnknownFreeSweep].  [Some] only with
     a refutation, as [Unsat] with the refuted clause's countermodel. *)
  and sweep_unknown_free ?(witness = WitnessConfig.default) pcsp =
    if not config.unknown_free_clauses.sweep then None
    else
      let senv = PCSP.Problem.senv_of pcsp in
      let formulas =
        List.map ~f:Ast.Evaluator.split_seq_reads_for_validity
        @@ UnknownFreeSweep.formulas senv (PCSP.Problem.clauses_of pcsp)
      in
      if List.is_empty formulas then None
      else
        let per_query, whole =
          Option.value (ZeroUnknownConfig.Switch.quick_sweep config.zero_unknown)
            ~default:(500, 5000)
        in
        let started = Common.Clock.now_s () in
        let deadline = started +. (Float.of_int whole /. 1000.) in
        let ask phi =
          Z3Smt.Z3interface.with_rlimit ~label:"ladder" config.zero_unknown.budgets.query_rlimit
          @@ fun () ->
          (if config.zero_unknown.rewrites.seq_as_array then
             Z3Smt.Z3interface.check_valid_seq_as_array
           else Z3Smt.Z3interface.check_valid)
            ~timeout:(Some per_query) ~fresh_solver:false ~id:None
            (Ast.LogicOld.get_fenv ()) phi
        in
        let result =
          UnknownFreeSweep.sweep ~split:config.zero_unknown.pieces.split_clause_heads
            ~expired:(fun () -> Float.(Common.Clock.now_s () >= deadline))
            ~ask formulas
        in
        Debug.print
        @@ lazy
             (sprintf
                "[unknown-free sweep] %d clause(s) without an unknown, %d \
                 unknown(s) left: %s in %.2f s"
                (List.length formulas) (Map.Poly.length senv)
                (match result with
                | Some (i, _, _) -> sprintf "clause %d refuted" i
                | None -> "nothing refuted")
                (Common.Clock.now_s () -. started));
        Option.map result ~f:(fun (_, piece, model) ->
            let model =
              Ast.LogicOld.Formula.and_of
              @@ List.filter_map model ~f:(fun ((x, sort), t) ->
                  Option.map t ~f:(fun t ->
                      Ast.LogicOld.Formula.eq
                        (Ast.LogicOld.Term.mk_var x sort)
                        t))
            in
            let unsat_witness =
              if WitnessConfig.records_unsat witness then
                Some
                  (UnsatWitness.make ~problem:(Some pcsp) senv
                     (UnsatWitness.Countermodel
                        {
                          formula = piece;
                          model;
                          witnesses =
                            lazy_witnesses
                              ~timeout:(Some config.zero_unknown.budgets.query_ms)
                              piece model;
                        }))
              else None
            in
            Ok
              ( PCSP.Problem.Unsat (Option.map unsat_witness ~f:payload_of),
                {
                  State.num_cegis_iters = 0;
                  unsat_witness;
                  kind_certificates = Map.Poly.empty;
                } ))
end

let make (config : Config.t) (context : Context.t) =
  (module Make
            (struct
              let config = config
            end)
            (struct
              let context = context
            end) : CoordinatorType)
