(** Validator *)

open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open PCSatCommon
open Ast
open Ast.LogicOld

module type ValidatorType = sig
  val run_phase : int -> State.s -> State.u Or_error.t

  val houdini_before_synthesis : State.u -> State.u option
  (** the Houdini-style pre-pass over the declared candidate atoms, asked once
      before the first synthesis; [None] leaves the loop as it would have
      been; with [houdini_after_seconds = Some _] it always gives [None] *)

  val houdini_at_round_boundary : elapsed_s:float -> State.u -> State.u option
  (** the same pre-pass asked lazily at a round boundary after the first,
      [elapsed_s] seconds after the coordinator's loop started: it runs only
      with [houdini_after_seconds = Some t], [elapsed_s >= t] and the pre-pass
      not yet run in this solve; [None] otherwise and whenever the eager form
      would give [None] *)

  val houdini_in_parallel : bool
  (** the configuration's [houdini_in_parallel] (with
      [houdini_before_synthesis]): the coordinator races the pre-pass in a
      forked copy ([houdini_parallel_prepass]) against the loop, and the two
      forms above then give [None] *)

  val houdini_parallel_prepass : State.u -> State.u option
  (** the pre-pass as the forked copy of [houdini_in_parallel] runs it, under
      [houdini_parallel_budget_ms] (else [houdini_budget_ms]): [Some (Sat
      sol)] for a fixed point that passed the final check at any time, the
      state with its counterexamples added for one that did not when that
      came within [houdini_budget_ms] (and [houdini_feedback_counterexamples]
      is on), [None] otherwise *)

  val houdini_seq_instantiation : bool
  (** the configuration's [houdini_seq_instantiation]: whether the pre-pass
      asks its sequence-existential questions by witness instantiation, for
      which the caller must set [SeqInstantiation]'s switches first *)
end

(** configuration of validator *)
module Config = struct
  type cex_strategy = AllExamples | ExamplesUpTo of int [@@deriving yojson]

  (* how a sequence-existential question of the Houdini fixed point is asked
     ([houdini_question_mode]) *)
  type question_mode = Plain_first | Switch | Dovetail | Race
  [@@deriving yojson]

  type t = {
    verbose : bool; [@default false]
    parametric_candidates : bool; [@default true]
        (* whether parametric candidate solutions are enabled *)
    parametric_examples : bool; [@default true] (* whether parametric examples are enabled *)
    strategy_synthesis : bool; [@default false] (* require that parametric_examples = true*)
    smt_timeout : int option; [@default None]
    houdini_declared_atoms : bool; [@default false]
        (** before the first candidate is checked, try the Houdini-style
            fixed point of the candidate atoms the input declares
            ([houdini_candidate]); it is reported only when it satisfies every
            clause, and otherwise the round goes on as it would have *)
    houdini_before_synthesis : bool; [@default true]
        (** run that pre-pass once before the first synthesis instead of
            inside the first validation (this switch runs it whether or not
            [houdini_declared_atoms] is set): the coordinator asks
            [houdini_before_synthesis] before the first round, answers at once
            when the fixed point satisfies every clause, and otherwise starts
            the loop as it would have -- so a first candidate that the
            declared atoms already give does not wait for a synthesis *)
    houdini_feedback_counterexamples : bool; [@default false]
        (** when the pre-pass's fixed point is not a solution, add the
            counterexamples of its failed final check to the examples, as the
            counterexamples of a rejected candidate are added.  They come from
            the ordinary check ([find_all_counterexamples]) with their
            derivations recorded, so they are sound examples; before the first
            synthesis they go through the phases that follow validation (the
            labeling and resolution) before the synthesizer sees them, and
            inside the first validation they join that round's
            counterexamples.  When off, a fixed point that is not a solution
            leaves nothing behind *)
    houdini_after_seconds : int option; [@default None]
        (** run the pre-pass of [houdini_before_synthesis] lazily: [Some t]
            moves it from before the first round to the first round boundary
            at which at least [t] seconds of wall-clock time have passed since
            the coordinator's loop started.  Contract, with
            [houdini_before_synthesis] on:
            - [None]: exactly the eager behaviour above (before the first
              synthesis, at most once);
            - [Some t]: nothing is asked before the first round; at a later
              round boundary the coordinator asks
              [houdini_at_round_boundary ~elapsed_s], which runs the pre-pass
              iff [elapsed_s >= t] and it has not run in this solve, so it runs
              at most once; its outcome is used as the eager one's is (a
              solution is the answer; otherwise, with
              [houdini_feedback_counterexamples], its counterexamples are added
              and processed by the phases after validation before the next
              synthesis; otherwise the round goes on as it would have);
            - a problem answered before [t] seconds never runs the pre-pass;
            - the pre-pass inside the first validation
              ([houdini_declared_atoms]) is not moved: it still runs there,
              and once it has run the lazy pre-pass does not.
            The reason: the pre-pass with generated candidates spends up to
            [houdini_budget_ms] before CEGIS starts, which a problem CEGIS
            answers quickly pays for nothing; run after [t] seconds, it is paid
            only by problems that CEGIS has not answered by then. *)
    houdini_in_parallel : bool; [@default true]
        (** with [houdini_before_synthesis], run the pre-pass in a forked copy
            of the process at the point where it would run before the first
            synthesis, concurrently with the loop, which starts at once as if
            the pre-pass had found nothing.  The first to finish wins, and
            the winner is always a run the sequential mode could make:
            - the loop answers first: the copy is killed;
            - the copy's fixed point passes its final check (within
              [houdini_parallel_budget_ms]): the copy becomes the run, answers
              [sat] with it, and the process exits with the copy's status,
              printing nothing more;
            - it fails within [houdini_budget_ms] (the sequential budget) and
              [houdini_feedback_counterexamples] is on: the copy becomes the
              run with the counterexamples added, exactly as the sequential
              pre-pass would have left it, the loop's progress meanwhile
              discarded (the sequential mode would not have had it either);
            - otherwise (it fails later, or spends its budget): the copy
              leaves and the loop goes on.
            The copy cannot send its result back instead of taking over: a
            solution or an example is a term of the extensible-variant term
            language, which does not survive [Marshal].  In this mode
            [houdini_after_seconds] is ignored, and the pre-pass inside the
            first validation ([houdini_declared_atoms]) is not run.  When the
            copy cannot be forked (a process with a domain), the copy's
            pre-pass runs in the process before the loop, sequentially. *)
    houdini_parallel_budget_ms : int option; [@default None]
        (** the pre-pass's budget under [houdini_in_parallel]; [None]:
            [houdini_budget_ms] *)
    houdini_parallel_unbounded : bool; [@default true]
        (** under [houdini_in_parallel], give the copy's pre-pass no budget of
            its own (overriding [houdini_parallel_budget_ms]): it runs until it
            ends or the process it was forked from ends.  The copy watches its
            parent and kills its own process group when the parent dies, so an
            outer time limit (a [timeout] around the run) bounds it, and the
            solver itself knows no overall time limit to size a budget by.
            The pre-pass only shrinks a finite candidate set, so without an
            outer limit it still ends.  Costs one core and the copy's memory
            for as long as it runs. *)
    houdini_extracted_qualifiers : Qualifier.Generator.Config.t ext_file option;
        [@default
          Some (ExtFile.Filename "./config/pcsat/qualifier/tb_cell.json")]
        (** give the pre-pass, beside the declared atoms, the qualifiers the
            given qualifier generator produces for each unknown before any
            example exists -- the call the array and DNF templates make for
            their extracted qualifiers ([generate] with no labeled atom and no
            example), so it is the same extraction, normalisation and
            propagation, read from the same kind of generator config (the
            default template's is [./config/pcsat/qualifier/tb_cell.json]).
            Each qualifier is offered in both polarities, as a template hole
            may take it either way; one with a free variable other than the
            unknown's parameters (a cell column) or an unknown is not offered,
            while a quantified one over the parameters is.  The generator is instantiated here, from
            the problem the validator was built with, so the candidates do not
            depend on whether the synthesizer's own extraction has run by the
            time the pre-pass fires.  The default names the default
            template's generator, so a chain gets the extraction without
            stating it; the path is read relative to the working directory,
            as every nested config path is, and a config writes [null] to
            switch it off.  On the Rust-derived contract inputs the pre-pass
            with all of its generated classes on (the defaults below) and a
            30 s pre-pass budget answered 71 of 110 runs of 120 s against 30
            without it; the four files on which it lost answers lost one to
            three of five.
            [None]: no extracted qualifier. *)
    houdini_defined_body_atoms : int; [@default 24]
        (** give the pre-pass the atoms of the input's non-recursive Bool
            definitions (a contract's pre- or postcondition, say) instantiated
            at the terms the unknown's parameters reach, at most this many per
            unknown -- the enumeration the array template's
            [defined_body_quals] makes, called with this limit.  [0]: none;
            the default 24 is the measured setting of the generated classes,
            which are on together (see [houdini_extracted_qualifiers]). *)
    houdini_rec_fun_apps : int; [@default 0]
        (** give the pre-pass the applications of the input's recursive
            definitions ([define-fun-rec]) at the terms the unknown's
            parameters reach -- [x = f(t1, ..., tn)] for an integer- or
            real-valued [f], [f(t1, ..., tn)] for a Bool-valued one -- at most
            this many per unknown: the enumeration the array template's
            [rec_fun_app_quals] makes, called with this limit.  Quantifier-free,
            so under [houdini_max_candidates].  [0]: none *)
    houdini_max_candidates : int; [@default 128]
        (** how many candidate atoms an unknown may carry into the pre-pass
            when atoms are generated (the two switches above); the declared
            atoms are always kept, and the generated ones fill the remainder,
            the smallest by [Formula.ast_size] first.  The pre-pass asks, per
            pass, one question per remaining atom per (clause, head atom)
            pair, and makes at most one pass more than it has atoms, so the
            number of questions grows with the square of the cap in the worst
            case and linearly when most atoms go in the first pass, which is
            the common case (a generated atom that is not inductive fails
            there).  The default 128 is the setting the generated classes
            were measured with together; it is bounded in time by
            [houdini_budget_ms] rather than by the square above, since a
            spent budget drops every atom not yet confirmed.  Ignored when no
            atom is generated. *)
    houdini_max_membership_candidates : int; [@default 24]
        (** with a positive value, the contract memberships
            ([houdini_contract_memberships]) are taken out of
            [houdini_max_candidates] and given a quota of their own of this
            many, after every other family, in the generator's order (see
            [HoudiniCandidates.merge]'s [own_quotas]).  Why: a membership of a
            three-place relation over a sequence ([r(e.0, sk, s.0)], the loop
            history of an adapter) is larger than the oriented inequalities
            over the same terms, so under one ranking by size the default 96
            inequalities fill the cap before it; an input whose invariant
            needs that membership then lost it, and lowering the inequality
            quota to make room cost another input the two inequalities it
            needs.  Adding a family's own quota can only add questions; the
            fixed point is reported only after the ordinary check against
            every clause.  [0]: the memberships rank with the other
            quantifier-free atoms, as before. *)
    houdini_max_quantified_candidates : int; [@default 24]
        (** with a positive value, the quantified generated atoms of an
            unknown are kept apart from [houdini_max_candidates]: at most this
            many of them, the smallest first, beside the cap rather than
            inside it (see [HoudiniCandidates.merge]).  [0]: one ranking by
            size for all generated atoms, in which the quantified ones, being
            the largest, are the first a cap drops. *)
    houdini_frame_equations : int; [@default 24]
        (** offer the pre-pass at most this many equations [t1 = t2] between
            terms of one sort that two different parameters of an unknown
            reach ([HoudiniCandidates.frame_equations]); [0]: none *)
    houdini_contract_memberships : int; [@default 24]
        (** offer at most this many memberships of reached terms in the
            Boolean relations an unknown carries and in the input's
            non-recursive Boolean definitions
            ([HoudiniCandidates.memberships]); [0]: none *)
    houdini_oriented_inequalities : int; [@default 96]
        (** offer at most this many sign facts, orders and difference bounds
            over the integer terms an unknown reaches
            ([HoudiniCandidates.inequalities]); [0]: none *)
    houdini_quantified_facts : int; [@default 24]
        (** offer at most this many of the problem's own quantified
            subformulas instantiated at the terms an unknown reaches
            ([HoudiniCandidates.quantified_facts]); [0]: none *)
    houdini_relation_inclusions : int; [@default 24]
        (** on by default (24), with [houdini_max_inclusion_candidates = 24]
            and [houdini_inclusions_second_round]: together they answered 47
            of 105 Rust-derived inputs where the configuration without them
            answered 40, losing none and contradicting no answer.
            Offer at most this many inclusions
            [forall x. R(t1, x) => R(t2, x)] between two reached terms of a
            relation's first argument, for the Boolean relations an unknown
            carries and the input's non-recursive Boolean definitions of two
            or more formals ([HoudiniCandidates.inclusions]); being
            quantified, they fall under [houdini_max_quantified_candidates]
            when that is positive and [houdini_max_inclusion_candidates] is
            [0]; [0]: none *)
    houdini_max_inclusion_candidates : int; [@default 24]
        (** on by default (24), with [houdini_relation_inclusions = 24] and
            [houdini_inclusions_second_round], for the reason given at the
            first.  With a positive value, the inclusions
            ([houdini_relation_inclusions]) have a quota of their own, outside
            both [houdini_max_candidates] and
            [houdini_max_quantified_candidates]: the atoms the other classes
            keep are exactly those they keep with the inclusions off, and at
            most this many inclusions, the smallest first, are added beside
            them ([HoudiniCandidates.merge]).  Ranked with the other quantified
            atoms, the inclusions (small universals) took the whole quantified
            quota on Rust-derived loops and displaced the contract's pointwise
            facts that the pre-pass answered those inputs from.  Generating
            them is inside [houdini_budget_ms] as every class is; but each
            atom added here is one more question per (clause, head atom) pair
            in each pass of the fixed point, so a quota costs fixed-point time
            in proportion to it, bounded only by the same budget.  [0]: the
            inclusions are ranked with the other generated atoms. *)
    houdini_exists_memberships : int; [@default 24]
        (** offer at most this many existential memberships
            [exists t. r[.., t, ..]] and [exists t. r[.., t, ..] /\ len t + x
            = y] for a Boolean relation an unknown carries whose index sorts
            are all reached but one, a sequence sort
            ([HoudiniCandidates.exists_memberships]): the history a loop
            keeps, which no term over the parameters denotes.  They have a
            quota of their own of the same size, outside
            [houdini_max_candidates], [houdini_max_quantified_candidates]
            and the inclusions' quota, as the inclusions do with
            [houdini_max_inclusion_candidates]: the atoms the other classes
            keep are exactly those they keep with this family off.  Their
            questions bind a sequence existentially, which
            [houdini_seq_instantiation] is for.  [0]: none *)
    houdini_array_pair_memberships : bool; [@default true]
        (** with [houdini_exists_memberships], the family also takes as the
            history's sort a single-constructor datatype of exactly an
            [Int]-indexed array and an [Int] (the array-plus-length encoding
            of a sequence that Rust-derived inputs over Creusot's [Seq] use):
            [exists a l. r[.., c(a, l), ..]] and [exists a l. r[.., c(a, l),
            ..] /\ l + x = y].  Without it only a sequence sort is taken, as
            before.  A candidate atom like any other: it is kept only when
            the fixed point proves it, and the fixed point is reported only
            after the ordinary check against every clause. *)
    houdini_array_existentials : bool; [@default false]
        (** with [houdini_seq_instantiation], a pre-pass question that binds
            an [Int]-indexed array existentially (a positive [exists] or a
            negative [forall]) takes the route a sequence-existential one
            takes: the plain question first under
            [houdini_seq_plain_first_ms], then the witness instantiation,
            whose forms include the pointwise array witnesses.  Each form
            implies its question, and a counterexample is still only a model
            of the negation, so the answers mean what the plain route's do.
            Why: the array-plus-length history of an iterator loop is such an
            existential, and the plain question leaves it undecided over
            arrays. *)
    houdini_guarded_frame_equations : int; [@default 48]
        (** offer at most this many guarded frame equations [x = y => u = v]
            ([HoudiniCandidates.guarded_frame_equations]): a frame equation
            between two parameters' reached terms that holds only until a
            counter reaches its bound ([n = e.1 => s.0 = e.0]: no iteration
            yet, so the inner state is untouched).  They have a quota of their
            own of the same size, after the existential memberships', so the
            atoms the other classes keep are those they keep with this family
            off.  [0]: none *)
    houdini_empty_guarded_frames : int; [@default 24]
        (** offer at most this many empty-guarded frame equations
            [len s = 0 => u = v] ([HoudiniCandidates.empty_guarded_frames]):
            a frame equation between two parameters' reached terms that holds
            while a reached sequence, the history a loop keeps, is still
            empty ([len sk = 0 => m.0 = s.0]: nothing drained yet, so the
            inner iterator is the one the adapter was built from).  They have
            a quota of their own of the same size, after the guarded frame
            equations', so the atoms the other classes keep are those they
            keep with this family off.  Adding candidates can only change
            which fixed point is found, and the fixed point is reported only
            after the ordinary check against every clause.  [0]: none *)
    houdini_seq_plain_first_ms : int option; [@default Some 1000]
        (** with [houdini_seq_instantiation], a sequence-existential question
            of the pre-pass is first asked as the pre-pass asks every other
            question ([check_clause_nonparam_smt]: the clause's negation, its
            own forking and weakening switches included) under a budget of at
            most this many milliseconds, and goes to the witness instantiation
            only when that answer is neither a proof nor a counterexample.  It
            is the question the pre-pass asks without
            [houdini_seq_instantiation], so it decides nothing that route would
            not decide: a proof is an [unsat] of the negation and a
            counterexample a model of it.  Why: the instantiation builds its
            forms in OCaml at 0.5-0.9 s a question, so on an input whose fixed
            point asks about a hundred such questions it spends the pre-pass's
            budget before the fixed point is reached, while most of those
            questions are decided by the plain question in milliseconds.
            [None]: the instantiation is asked first, as before *)
    houdini_seq_question_ms : int option; [@default Some 2000]
        (** with [houdini_seq_instantiation], the witness-instantiation route
            of one sequence-existential question of the pre-pass's fixed
            point (its instantiated forms, its pinned and length-bounded
            refuters, the zero-unknown verdict's ladder, and the unrewritten
            question asked last) is given at most this many milliseconds: the
            pre-pass's deadline is narrowed to that for the question and
            restored after it, so every solver call on the route is given at
            most what is left, and once it is spent no further form is built
            or asked and the question is answered [`Timeout], as a question
            that ran out of the pre-pass's own budget is.  A proof found
            before that is still a proof and a model still a counterexample,
            so the cap can only leave a question undecided, and its candidate
            atom is then dropped; the fixed point is still checked against
            every clause before it is reported.  The final check's questions
            are not capped: one cut short there would reject the whole fixed
            point, not one atom, and send the pre-pass into another round.
            Why: the route asks dozens of solver questions of up to 10 s
            each, and on an input whose existential candidates it cannot
            prove it spent 5-19 s on each of a handful of questions, so the
            fixed point ran past the pre-pass's budget and nothing was
            reported, while the questions the route did prove were proved
            within about 2 s.  [None]: no cap but the pre-pass's own *)
    houdini_seq_instantiation : bool; [@default true]
        (** inside the pre-pass (its fixed point and the final check of the
            fixed point), ask a question that binds a sequence existentially
            -- a positive [exists] or a negative [forall] over a variable of
            sequence sort, which an existential candidate atom such as
            [exists t. len t + n = m /\ r(a, t, b)] puts there in a head and
            in a body -- through [SeqInstantiation.decide_clause]: first its
            instantiated forms (each positive sequence existential replaced
            by a term the clause builds, [x0 ++ x1] for a chained pair of
            applications among them, each positive universal skolemised),
            each of which implies the question, so a proof of one ends it as
            valid; then the pinned refuters, whose models are models of the
            question's own negation; and only then the question asked
            without the switch, whose answer is returned as it is.  So the
            switch can only prove valid what was otherwise undecided: a
            question it answers valid is valid, a counterexample it returns
            is one, and it never makes a fixed point that is not inductive
            look like one -- it cannot produce an [unsat], since the
            pre-pass reports only solutions.  The witness instantiation is
            the one the zero-unknown verdict uses, with its switches set from
            the coordinator's [*_no_unknown_query] fields before the pre-pass
            (and so also for the read-back route afterwards).  When off, every
            question is asked as before and those switches are left alone. *)
    houdini_last_element_equations : int; [@default 24]
        (** offer at most this many equations [v = s[len t]] between a
            reached term and the entry of a reached sequence at the length of
            another ([HoudiniCandidates.last_element_equations]): the current
            value a loop also keeps as the last entry of a ghost history
            ([g = fs[len s]], the closure state beside the history of
            produced items), which no other family offers.  On its own quota,
            after every other family, so it takes no place from them and adds
            at most this many questions per pass.  [0]: none *)
    houdini_length_sums : int; [@default 24]
        (** offer at most this many equations [len s + x = t] between a
            reached sequence's length, a shift [x] (zero or a reached integer
            term) and a target [t] (a reached integer term or another reached
            sequence's length) -- the count a loop keeps between the items it
            has collected and an iterator's positions ([len out + a.0 = b.0])
            ([HoudiniCandidates.length_sums]).  Quantifier-free, so under
            [houdini_max_candidates].  [0]: none *)
    houdini_affine_elements : int; [@default 24]
        (** offer at most this many universals
            [forall i. 0 <= i < len s => s[i] = t + i] for a reached sequence
            [s] of integers and [t] zero or a reached integer term -- the
            content of a sequence collected from a counting range
            ([HoudiniCandidates.affine_elements]).  Being quantified, they
            fall under [houdini_max_quantified_candidates] when that is
            positive and [houdini_max_affine_candidates] is [0]; [0]: none *)
    houdini_prefix_elements : int; [@default 24]
        (** offer at most this many prefix universals
            [forall i. 0 <= i < x => s[i] = c] for a reached sequence [s] of
            integers, a reached integer term [x] (another reached sequence's
            length included, never [len s]) and [c] one of the four integer
            literals of the input smallest in absolute value
            ([HoudiniCandidates.prefix_elements]): the part of a sequence a
            loop has already overwritten, below its position.  They have a
            quota of their own of the same size, after the empty-guarded
            frame equations', so the atoms the other classes keep are those
            they keep with this family off.  [0]: none *)
    houdini_max_affine_candidates : int; [@default 24]
        (** with a positive value, the affine element universals
            ([houdini_affine_elements]) have a quota of their own outside both
            caps, as [houdini_max_inclusion_candidates] gives the inclusions:
            the atoms the other classes keep are exactly those kept with the
            family off, and at most this many affine universals, the smallest
            first, are added after them.  [0]: ranked with the other
            generated atoms. *)
    houdini_guarded_orders : int; [@default 24]
        (** offer at most this many orders guarded by a sequence's emptiness,
            [len s = 0 \/ t1 <= t2], for a reached sequence [s] and two
            distinct reached integer terms ([HoudiniCandidates.guarded_orders])
            -- the bound a loop keeps only once it has produced something
            ([len out = 0 \/ b.0 <= b.1]: an iterator that produced an item
            was not past its end), which an unguarded order cannot state when
            the empty case starts from an arbitrary range.  Quantifier-free,
            so under [houdini_max_candidates] unless
            [houdini_max_counting_candidates] is positive.  [0]: none *)
    houdini_max_counting_candidates : int; [@default 72]
        (** with a positive value, the length sums, the three-term equations
            and the guarded orders ([houdini_length_sums],
            [houdini_three_term_equations], [houdini_guarded_orders]) have a
            quota of their own outside both caps, with the contract of
            [houdini_max_inclusion_candidates]: the atoms the other classes
            keep are exactly those kept with these families off, and at most
            this many of theirs, the smallest first, are added after the
            inclusions and the affine universals.  Ranked with the
            quantifier-free atoms under [houdini_max_candidates], they are
            larger than the sign facts and orders of the other families, and
            a needed three-term equation was cut by the cap before a question
            was asked about it.  [0]: ranked with the other generated atoms. *)
    houdini_three_term_equations : int; [@default 24]
        (** offer at most this many equations [x = y - z] between three
            distinct reached integer terms (sequence lengths included), one
            of [x = y - z] and [z = y - x] for each, the smallest first
            ([HoudiniCandidates.three_term_equations]): an exact count kept
            between a counter and two positions ([n = b.0 - it0.0]).
            Quantifier-free, so under [houdini_max_candidates].  [0]: none *)
    houdini_inclusions_skip_constructor_equations : bool; [@default false]
        (** with [true] (and [houdini_frame_equations] positive), an inclusion
            built from a definition whose inlined body is a constructor
            equation over the varied first formal is not offered when the
            frame family offers the equation it is equivalent to
            ([HoudiniCandidates.constructor_equation_body] states the test and
            the equivalence).  On a Rust-derived loop such relations
            ([h2 = mut a h1]) were 330 of the 336 inclusions offered, each
            equivalent to an equation [t1 = t2] and each one more question per
            pass of the fixed point.  The quota
            [houdini_max_inclusion_candidates] then goes to the remaining
            inclusions. *)
    houdini_inclusions_second_round : bool; [@default true]
        (** on by default, with both inclusion counts at 24, for the reason
            given at [houdini_relation_inclusions]; the second round is what
            keeps the inclusions from costing the inputs the pre-pass answers
            without them.  With [true], [houdini_relation_inclusions] positive and
            [houdini_max_inclusion_candidates] positive, the pre-pass runs in
            up to two rounds instead of one ([HoudiniCandidates.rounds]):
            - round 1 is the pre-pass with no inclusion generated: the same
              candidates, in the same order, under the same
              [houdini_budget_ms], as with [houdini_relation_inclusions = 0];
              a fixed point that passes the final check is the outcome and
              nothing else is asked;
            - only when round 1's fixed point fails the final check (it has
              counterexamples and the budget was not spent), round 2 runs the
              fixed point from the FULL round-1 candidate set (not its
              survivors) plus the inclusions -- the pre-pass this switch off
              would run -- under a fresh budget
              ([houdini_inclusion_round_budget_ms], else
              [houdini_budget_ms]); its outcome replaces round 1's, so round
              1's counterexamples are dropped and only round 2's are fed back
              under [houdini_feedback_counterexamples];
            - when round 1 spends its budget, or has nothing to try, round 2
              does not run (a superset of the candidates would spend it too).
            Each round's outcome is the ordinary final check of an inductive
            conjunction, so soundness is that of one round.  Why: an
            inclusion, once offered, is a hypothesis of every inductive
            question until a pass refutes it, and on inputs answered from the
            pre-pass alone those extra hypotheses turned a few questions into
            per-question timeouts, each dropping an atom of the solution;
            while an atom inductive only relative to an inclusion needs the
            full candidate set beside the inclusion, which a round started
            from round 1's survivors would no longer hold.  Cost: up to two
            budgets on an input both rounds fail.  With [false] (or either
            count [0]) the questions asked are exactly the one-round
            pre-pass's. *)
    houdini_inclusion_round_budget_ms : int option; [@default None]
        (** round 2's own wall-clock budget under
            [houdini_inclusions_second_round]; [None]: [houdini_budget_ms]
            (and no budget when that is [None]) *)
    houdini_declared_first : bool; [@default false]
        (** before the pre-pass proper, run it once over the declared
            candidate atoms alone ([PCSP.Params.candidate_atoms]; nothing
            generated), and answer with that fixed point when it passes its
            final check; otherwise the pre-pass runs as without the switch.
            The point is an atom set already known to be a solution when it
            is one at all -- the graph [PCSP.RecFunGraph] records for each
            unknown it introduces -- which, diluted among the generated
            atoms, waits behind every question about them.  Contract: the
            first run returns only a fixed point that passed the ordinary
            final check, so a [sat] from it is sound exactly as the
            pre-pass's is; when it does not answer, the second run is the
            pre-pass of this configuration as it would have been, with its
            own budget.  [false]: one run, generated and declared atoms
            together *)
    houdini_budget_ms : int option; [@default Some 30000]
        (** a wall-clock budget, in milliseconds, for the whole pre-pass --
            generating its candidates and asking its questions, not the final
            check of its fixed point, which is the ordinary check of a first
            candidate.  Each question is given at most what is left of it, and
            once it is spent no further question is asked: every atom not yet
            confirmed counts as undecided and is dropped, which empties the
            conjunctions, so the pre-pass reports that it has nothing to try
            and the round goes on as it would have.  A spent budget therefore
            never changes an answer; it only bounds what the pre-pass costs.
            [None]: no budget beyond each question's own. *)
    houdini_atom_countermodel_drops : bool; [@default true]
        (** in the pre-pass's fixed point, the countermodel that refutes one
            atom's own question is also judged against the atoms of the same
            clause still to be asked in the pass, and every atom it makes
            false ([HoudiniByModel.judge]) is dropped without a question of
            its own.  A question answered in a forked copy (with
            [houdini_fixed_point_verdict_only] no model comes back) is judged
            in the copy, which sends back only the positions of the refuted
            atoms; a question answered in this process by a plain solver
            check is judged here.  Sound for the same reason as
            [houdini_drop_by_model]: within a pass the body of a clause's
            questions is fixed, so a model of [body /\ ~a] in which [b] is
            false is a model of [body /\ ~b], which refutes [b]'s own
            question.  The judge is bound to the very formula asked
            (physical identity), so a model of a strengthened or rewritten
            form asked on the way is never read as one of the question.  The
            fixed point is unchanged whenever every question decides; what
            changes is how many questions it takes. *)
    houdini_shared_body_session : bool; [@default true]
        (** in the pre-pass's fixed point, before a clause's question about a
            candidate head is asked, try to prove it against the clause's body
            held in one solver: per clause and pass the body's negation is
            simplified, the conjuncts [Z3interface.may_not_return] refuses are
            set aside, and the rest is converted and asserted once
            ([Z3interface.base_session_set]); each head's negation is then
            checked against it in a scope ([base_session_unsat]).  An [unsat]
            proves the question valid -- the rest is implied by the body's
            negation, so [rest /\ ~head] unsatisfiable makes [body \/ head]
            valid -- and the question is not asked.  Any other answer leaves
            the question to be asked as before, so the fixed point is the same
            whenever every question decides; what changes is that a valid
            atom's question, which converted and asserted the whole body
            (tens of conjuncts) every time, now converts one head.  A head
            whose negation the solver may not return from is never tried
            here. *)
    houdini_fixed_point_verdict_only : bool; [@default true]
        (** in the pre-pass's fixed point, a question answered satisfiable by
            a forked copy (the questions a solver may not return from are
            asked in one) is not asked again in this process for its model:
            the fixed point reads only whether the clause holds, so the
            question's answer is the copy's, with an empty model.  The fixed
            point and the questions it asks are the same whenever the asking
            again would also have answered satisfiable; when it would not
            have, the atom is dropped either way, and only whether the
            question counts as timed out differs, which matters only with
            [houdini_skip_clause_after_timeout].  The final check, which
            builds counterexamples from the models, asks again as before.
            What it saves is that second, in-process question, one per atom a
            forked question refutes. *)
    houdini_skip_clause_after_timeout : bool; [@default false]
        (** in each pass of the pre-pass's fixed point, once a question about
            a clause has run out of its budget (a timeout, or a forked copy
            killed at its budget), ask nothing more about that clause in that
            pass: every atom still to be asked there, for any of its head
            atoms, counts as undecided and is dropped, exactly as a spent
            [houdini_budget_ms] drops it, and the pass goes on with the next
            clause.  A later pass asks the clause again.  Dropping atoms can
            only shrink the fixed point, which is reported only after the
            ordinary check against every clause, so this can lose an answer the
            pre-pass would have found and never produce a wrong one; it stops
            one clause whose questions do not return from spending the whole
            budget *)
    houdini_quantified_facts_frame_only : bool; [@default true]
        (** with [houdini_quantified_facts] positive, each input fact the
            family instantiates that has a free variable of an opaque sort (a
            sort variable, an uninterpreted sort, a datatype; not an integer
            or a sequence, whose facts are ranges over a moving counter) some
            term reached from the unknown's frame parameters has (the parameters
            every loop of the unknown passes on unchanged,
            [HoudiniCandidates.frame_positions]) is instantiated with those
            terms only, in place of its instances of before; the facts
            instantiated are the same ([quantified_facts ~frame]).  A
            precondition over a function's arguments stays true over a loop
            that keeps them, while its instances at the moving values were
            each asked, not inductive, and often left undecided at the
            question's whole budget, and the instance at the kept values could
            fall outside the instance limit.  Changes only which candidates
            are offered: can lose an answer, never make one wrong. *)
    houdini_drop_premise_atoms : bool; [@default true]
        (** leave out of the pre-pass's candidates a generated atom that
            every clause applying the unknown already has as a premise at
            each application ([HoudiniCandidates.premise_redundant]): a law of
            a universal the unknown carries, which the reader put into each
            such clause.  It cannot change whether a clause holds, and cost a
            question per clause and pass and a hypothesis in every other
            question. *)
    houdini_final_seq_axiom_first : bool; [@default true]
        (** in the pre-pass's final check of its fixed point, ask a clause
            that mentions a sequence first in the sequence-axiom form
            ([Z3interface.with_seq_axiom_fallback], under its process-wide
            budget), and read a proof there as the clause's validity; anything
            else asks the ordinary question as before (with
            [clause_check_seq_axiom_fallback] not asking the axiom form
            again).  Why: the fixed point is a large conjunction over
            sequences, the native sequence theory left three of five final
            questions undecided at their whole budget (5-8 s each, killed
            copies), and the axiom form then proved each in about 0.2 s.
            Sound as the fallback is: an axiom proof is a proof. *)
    houdini_memo_questions : bool; [@default true]
        (** inside one pre-pass, a question printed exactly as one already
            decided gets the same answer without being asked again (only
            decided answers are kept).  Why: in each pass of the fixed point
            the clauses whose body does not apply the unknown, and the step
            clauses whose hypothesis the previous pass left unchanged, ask
            the same questions again; on a fold loop 265 of 365 questions were
            textual repeats of earlier ones (8 s of 24 s).  The same formula
            under the same problem has the same validity, so the fixed point
            is the one without the field. *)
    houdini_drop_by_model : bool; [@default true]
        (** in each pass of the pre-pass's fixed point, before asking about
            one atom at a time, ask a (clause, head atom) pair once with the
            conjunction of every atom still held as the head (classic
            Houdini): when that question is proved every atom is kept without
            a question of its own; when it is refuted, each atom that the
            countermodel makes [false] (substituted and simplified; an atom
            the simplifier leaves undecided, such as one binding a sequence
            existentially, is not judged) is dropped, and the conjunction of
            the rest is asked again, until a question is proved, undecided,
            or drops nothing; the atoms still held then get the per-atom
            questions as before.  Why: the pre-pass asked one question per
            atom, and with some 250 generated atoms over a large clause (an
            iterator adapter's loop) its 30 s budget ran out in the first
            clause at about 0.8 s a question.  An atom false in a model of
            the clause's body under the current candidate is one its
            per-atom question would refute with that same model, so when
            every question decides the fixed point is the one without the
            switch; an unsound countermodel (a weakened question's) can only
            drop more, and the fixed point is reported only after the
            ordinary check against every clause, so the switch can lose an
            answer and never produce a wrong one *)
    houdini_drop_by_model_solver_ms : int option; [@default None]
        (** with [houdini_drop_by_model], [Some ms]: an atom the countermodel
            leaves undecided after substitution and simplification (an
            application of a recursive function such as a datatype's size, a
            quantifier over the model's arrays, an existential over a
            sequence) is asked of the solver with the model's values
            substituted, in a forked copy killed after [ms] (capped by what is
            left of the pre-pass's budget): unsatisfiable makes it false in
            the model, so it is dropped; its negation unsatisfiable makes it
            true.  Why: on an iterator adapter's loop the atoms no
            substitution judged were left to their own clause questions, and
            four of those (existentials over the loop's history with a wrong
            length) took 31 s of a 41 s fixed point.  Sound as the model drop
            is: an atom is dropped only when false in the countermodel *)
    houdini_drop_by_model_quantified_aside : bool; [@default false]
        (** with [houdini_drop_by_model], an atom that is not quantifier-free
            is never put in the conjunction question, only judged against
            each of its countermodels (dropped when false in one) and
            otherwise left to its own question.  Why: with
            [houdini_drop_by_model_solver_ms] such atoms (existentials over a
            loop's history) are judged true and stay in the conjunction, and
            a conjunction holding dozens of sequence existentials was a
            question that did not return within the pre-pass's budget, where
            the same conjunction without them was proved or refuted in a
            fraction of a second *)
    houdini_atom_questions_prove_only : bool; [@default true]
        (** with [houdini_seq_instantiation], a per-atom question of the
            pre-pass's fixed point that takes the witness-instantiation route
            builds no refuter (neither the pinned nor the length-bounded
            ones), and runs in a forked copy killed at the pre-pass's
            deadline (narrowed by [houdini_seq_question_ms] when that is
            set): its atom is kept only when the question is proved, and a
            refutation drops it exactly as an undecided answer does, so a
            refuter can only cost time, and only the proof has to come
            back.  A conjunction question of
            [houdini_drop_by_model] and the final check keep their refuters,
            whose models those use.  Why: building one length-bounded refuter,
            or the ladder's forms, is not a solver call, so no budget cuts it
            short, and on an iterator adapter's loop two refuter
            constructions took 6 and 8.5 s, and one ladder's 10 s, of a fixed
            point the pre-pass's 30 s budget could not then hold *)
    houdini_drop_by_model_conjunction_ms : int option; [@default Some 6000]
        (** with [houdini_drop_by_model] and [houdini_seq_question_ms], [Some
            ms]: a conjunction question's witness-instantiation route is
            capped at [ms] instead of [houdini_seq_question_ms].  Why: one
            conjunction question decides many atoms, and cut short it leaves
            every held atom to its own question.  On an iterator adapter's
            loop (skip) a conjunction of 51 atoms was proved by the route in
            about 2 s, which a 1 s cap cut, and the fixed point then ran past
            the pre-pass's budget; on a generic fold an uncapped conjunction
            question ran 23 s and proved nothing.  [None]: the same cap as
            every other question *)
    houdini_simplify_shared_once : bool; [@default false]
        (** in the pre-pass's fixed point, the disjuncts a clause shares
            between its questions (its pure part and the other atoms, as
            converted once by [houdini_shared_conversion]) are simplified once
            per clause and pass, and each question is simplified from those
            and its own head ([Evaluator.simplify_with_leaf_cache]); the
            question is the one simplifying it whole gives, up to bound names.
            Why: each question is the whole clause with the current
            conjunction substituted, and simplifying the shared parts again
            for every atom was about 29 s of a fold loop's pre-pass (a quarter
            of it in Set.Poly), by a profiler *)
    houdini_memo_before_simplify : bool; [@default false]
        (** in the pre-pass's fixed point, a question printed exactly as one
            already decided in the same fixed point, before it is simplified,
            gets that answer (and its countermodel) without being simplified
            or asked.  The same formula simplifies to the same question, so
            the answers and the fixed point are the ones without the field.
            Why: [houdini_memo_questions] looks a question up only after
            simplifying it, which on a fold loop was most of the cost *)
    houdini_drop_by_model_batch_ms : int option; [@default None]
        (** with [houdini_drop_by_model], [Some ms]: once per countermodel,
            the atoms its substitution leaves undecided (quantified atoms,
            applications of a recursive function such as a datatype's size,
            reads of a relation at elements of an uninterpreted sort) are
            judged all together in one forked copy killed after [ms] (capped
            by the pre-pass's budget), each asked of Z3 with the model's values
            substituted and at most 500 ms: unsatisfiable makes it false in
            the model, its negation unsatisfiable true; an atom the copy does
            not decide, or a killed copy, leaves it to its own question.  Why:
            on a fold loop the countermodel left 68-80 of 136 atoms unjudged,
            and [houdini_drop_by_model_solver_ms] paid a fork per atom.  Sound
            as the model drop is: an atom is dropped only when false in the
            countermodel *)
    houdini_conjunction_plain_first_ms : int option; [@default None]
        (** with [houdini_drop_by_model], [Some ms]: a conjunction question's
            plain question (asked before the witness-instantiation route) gets
            [ms] in place of [houdini_seq_plain_first_ms].  Why: on a generic
            fold a conjunction of 11 atoms was left undecided by the plain
            question at its 1 s, then the route's ladder spent 11 s building
            forms without a proof, and the unrewritten question asked after it
            found the countermodel in 0.6 s; a conjunction question is mostly
            refuted, and its model is what drops atoms *)
    houdini_question_mode : question_mode; [@default Switch]
        (** with [houdini_seq_instantiation], how a sequence-existential
            question of the pre-pass's fixed point (a conjunction question of
            [houdini_drop_by_model] or a per-atom one) is asked, between its
            two searches -- the plain, unrewritten question, which finds a
            countermodel or a proof, and the witness-instantiation route,
            asked for a proof only -- within the question's cap (the
            pre-pass's deadline, narrowed by [houdini_seq_question_ms], or by
            [houdini_drop_by_model_conjunction_ms] for a conjunction):
            - [Plain_first]: as before this field ([houdini_seq_plain_first_ms],
              [houdini_conjunction_plain_first_ms], then the route);
            - [Switch]: the plain question for [houdini_seq_plain_first_ms]
              (the cap when that is unset), then the route once for the rest
              of the cap;
            - [Dovetail]: the plain question and the route in turn, in slices
              doubling from [houdini_dovetail_start_ms];
            - [Race]: both at once in two forked copies; the first decisive
              answer wins and the other copy is killed.
            In every mode the first decisive answer is taken: a countermodel
            or a proof from the plain question, a proof from the route.  The
            final check is asked as without the field. *)
    houdini_dovetail_start_ms : int; [@default 500]
        (** the first slice of [houdini_question_mode = Dovetail] *)
    houdini_fork_fresh_context : bool; [@default false]
        (** a question of the pre-pass asked in a killed copy is asked there
            in a Z3 context made for it alone rather than the pooled one.  The
            copy's answer is all that comes back, so the pooled context of this
            process is untouched either way.  Why: a refutable conjunction
            question that a fresh z3 answers in 0.04-0.1 s, under every replay
            condition tried, was killed at 1 s in the copy *)
    houdini_final_check_goals_only : bool; [@default true]
        (** the final check of the pre-pass's fixed point asks only the
            clauses with no unknown in the head.  Why it is sound: the fixed
            point is returned only after a pass that changed nothing, under
            the very candidate it returns, and in such a pass every (clause,
            head application) question was proved valid for every atom held
            -- an atom whose question is refuted, undecided or left unasked is
            dropped, and a drop is a change -- so for every clause with an
            unknown in its head, [body => atom \/ rest] is valid for each atom
            of the candidate, hence for their conjunction, which is the clause.
            A clause with no head application is never asked in the fixed
            point, so it is still checked.  Why: on a generic fold the final
            check spent 5-16 s re-proving, through the instantiation route, a
            clause the last pass had proved, and the pre-pass ran past its
            budget in one run of three *)
    houdini_final_check_by_pieces : bool; [@default true]
        (** in the final check of the pre-pass's fixed point, a clause whose
            question came back neither proved nor refuted is asked again by
            its pieces ([PCSatCommon.ClausePieces.of_clause]: the conjuncts of
            its negation normal form, a disjunction distributed within a
            bound), each with the question the check asks of a clause; when
            every piece is proved the clause holds, and otherwise the first
            answer stands.  Exact: the clause is the conjunction of its pieces
            in every model, and only proofs are taken from them.  Why: the
            goal clause of an iterator's [next] whose head is a conjunction of
            postconditions is left undecided whole while each [body => c] is
            decided at once; the zero-unknown verdict already asks such a
            clause by its pieces, and the pre-pass's fixed point is checked
            against the clauses before any resolution has split them.  Asked
            within what is left of [houdini_budget_ms]. *)
    houdini_final_check_retry_ms : int option; [@default None]
        (** in the final check of the pre-pass's fixed point (the ordinary
            check of the fixed point against every clause), a clause whose
            question ran out of its budget (a timeout, or a forked copy killed
            at it) is asked once more: the same question, the negation of the
            clause with the fixed point substituted, in a forked copy killed
            after this many milliseconds and asked there with no solver timer
            ([PCSatCommon.ForkedQuery.valid_within]).  Only its [unsat] is
            read, and the clause then holds; anything else keeps the timeout,
            so the outcome is the one without the field.  The retry is not
            counted against [houdini_budget_ms], and a clause the check did not
            reach because that budget ran out is not retried.  Sound: it can
            only add a proof that the clause is valid, and the fixed point is
            reported only when every clause was so shown.  [None]: no retry.
            Why: on a Rust-derived input the fixed point holds the solution's
            atoms and its final check was decided in 1 s on one run, while on
            others one clause's question was killed at the 5 s cap of a
            quantified question and the pre-pass reported nothing.  Off by
            default *)
    houdini_linear_subst : bool; [@default true]
        (** build each question of the pre-pass's fixed point with
            [Logic.Term.subst_rename_on_capture] instead of [Logic.Term.subst],
            and substitute the disjuncts a (clause, head atom) pair shares
            across its candidate atoms once per pass rather than once per
            atom.  The question is the same formula up to the names of bound
            variables ([subst_rename_on_capture]'s contract, the clause and the
            candidate lambdas being beta-normal).  [subst] reduces an
            application of an n-parameter candidate one argument at a time and
            renames the whole conjunction of candidate atoms at every step,
            so a question costs about n traversals of every candidate it
            mentions; here it costs one.  On by default: the questions are
            the same up to bound names, in the same order.  It draws fewer
            fresh names, which moves every later name and with it the loop's
            trajectory, and a pass that finishes sooner can ask questions a
            spent budget would not have; neither changes what is sound to
            report *)
    (* [true], with [houdini_linear_subst]: the parts of a pre-pass question
       that every atom asked against one clause shares -- the clause's pure
       part and its other literals, substituted once per pass -- are also
       converted to the first-order form once, and each question's formula is
       assembled from the converted parts and the converted head.  The
       conversion maps a Boolean constant to the same constant and a
       disjunction to the disjunction of the converted disjuncts, so the
       assembled formula is the one converting the whole question gives, and
       it is simplified and asked exactly as before: the same questions in the
       same order.  On by default: converting the whole question again for
       every atom asked against one clause was most of a question's cost
       beside its simplification, and with the shared parts converted once a
       pass reached a given question in a quarter to three fifths of the
       time on the two inputs measured.
       Without [houdini_linear_subst], or [false], each question is converted
       whole. *)
    houdini_shared_conversion : bool; [@default true]
    clause_check_axiom_first_when_proved : bool; [@default true]
        (** in validation, a problem clause whose counterexample question an
            earlier round's check proved valid only through the sequence-axiom
            form ([clause_check_seq_axiom_fallback]: the native question
            undecided, the axiom form a proof) is asked in the axiom form
            FIRST in every later round: a proof there is the answer, and
            otherwise the question is asked as before, without the axiom form
            a second time.  The same two questions are asked, in another
            order, so the answer is the one the default order gives (an axiom
            proof and a native countermodel cannot both exist, both being
            sound); only the time changes.  Why: on a Rust-derived input with
            composition clauses over sequences, the native question ran out of
            its 5 s budget on the same clauses round after round before the
            axiom form proved each in well under a second.  When off, the
            native question is always asked first. *)
    validation_by_pieces : (int * int) option; [@default None]
        (** [Some (axiom_ms, native_ms)]: in validation, a quantified clause
            question left undecided by the ordinary route (the native question,
            then the axiom form of the whole clause) is asked again piece by
            piece ([ClausePieces.of_clause]: the clause's negation normal form
            split at its head's conjunctions, the pieces' conjunction being
            the clause in every model): each piece in the sequence-axiom form
            under [axiom_ms], and, when that does not prove it, natively under
            [native_ms].  Every piece proved is the clause proved ([`Unsat]);
            a countermodel of one piece is a model of the clause's negation and
            is returned as the counterexample; anything else leaves the
            question undecided.  A clause decided this way is asked by pieces
            first in later rounds, and by the ordinary route only when that
            leaves it undecided.  Sound both ways, but not the same answers:
            it decides questions the ordinary route leaves undecided, and the
            countermodel it returns may differ.  Why: on a Rust-derived input
            the zero-unknown verdict's quick stage, which asks exactly this,
            proved or refuted in under 7 s several clause questions that the
            native question left undecided at 5 s and the whole clause's axiom
            form did not prove.  [None]: not asked. *)
    validation_memo_alpha : bool; [@default true]
        (** in validation, a clause question equal, up to the names of its
            bound variables, to one an earlier question of the same solve
            proved valid gets that answer without being asked.  Exact: the
            problem and its definitions do not change within a solve, and
            validity does not depend on bound names; the clause's own free
            variables (with their sorts) are part of the key, so only the same
            question is matched.  Only a proof is kept, never a countermodel
            (a new asking may give another one) nor an undecided answer.
            Why: a candidate that changes some unknowns leaves the others, and
            the clauses over those only, as they were, but each round
            substitutes them with fresh bound names; on a Rust-derived input
            about half of the quantified questions of four rounds were such
            repeats.  When off, every question is asked. *)
    validation_memo_undecided : bool; [@default false]
        (** with [validation_memo_alpha], a question equal up to bound names
            to one an earlier round left undecided under the same budget is
            answered [`Timeout] without being asked.  NOT exact: Z3 is not
            deterministic across contexts, and a question once undecided was
            observed decided on a later asking; with this on, such a later
            proof or countermodel is lost (the candidate is rejected and
            nothing learnt from the clause, as for any undecided answer).
            When off, an undecided question is asked again. *)
    defer_undecided_clauses : bool; [@default false]
        (** in validation, the problem clauses whose counterexample question
            an earlier round left undecided are asked after every other
            clause, and not asked at all when a clause asked before them has
            already given a counterexample: the candidate is rejected then
            whatever they answer, and an undecided answer adds no example.
            NOT exact: a deferred clause that this round would have refuted
            gives no counterexample, so the round learns fewer examples (never
            a wrong one).  When off, every clause is asked. *)
    clause_check_cvc5_retry_ms : int option; [@default None]
        (** with [Some ms], a clause's counterexample question that is still
            undecided after the sequence-axiom fallback (or without it) is
            asked once more as the validity of the clause, of cvc5 in a
            separate process under [ms] (capped by the Houdini window's
            remainder; [PCSatCommon.Cvc5Proof.valid_within]), and read as
            [unsat] only when cvc5 answers [unsat]; a [sat] from cvc5 is never
            read as a countermodel, and anything else leaves the undecided
            answer as it was.  So the field can only turn an undecided
            question into a proof of validity.  Why: of the validation
            questions on a Rust-derived input that Z3 left undecided at 5 s
            and the sequence axioms did not prove, cvc5 proved some in 2-7 s.
            [None]: never asked. *)
    clause_check_seq_axiom_fallback : bool; [@default true]
        (** when a clause's counterexample question (the Houdini pre-pass's
            questions and the validation of a candidate alike) comes back
            undecided -- a timeout or [unknown] -- and the clause mentions a
            sequence, ask once more whether the clause is valid with the
            sequences an uninterpreted sort and axioms about length, reads and
            concatenation ([Z3interface.with_seq_axiom_fallback], under the
            process-wide [seq_axiom_fallback] budget and never longer than the
            question's own), and read the question as [unsat] only when that
            proves the clause valid; any other outcome leaves the undecided
            answer as it was.  Sound: an axiom proof of the clause is a proof
            of it, so the switch can only turn an undecided question into a
            decided one and never decides one wrongly.  Why: the native
            sequence theory leaves undecided a step that pushes one element
            onto ghost sequences holding a chain [forall k < len s. R(s[k],
            s[k+1])], which the axiom form proves at once; the predicate
            eliminator and the zero-unknown verdict already ask that second
            attempt, the clause checks did not.  [false]: every question is
            answered as before. *)
    smt_timeout_quantified : int option; [@default Some 5000]
        (** the budget, in milliseconds, of a validation query whose clause
            still contains a quantifier after the candidate is substituted --
            a candidate read back from array or sequence cells puts a universal
            over the cell index into every clause it occurs in, and a premise
            universal stays universal in the counterexample query, which the
            solver can take minutes over.  Only such queries get this budget
            (the smaller of it and [smt_timeout]); a quantifier-free query keeps
            [smt_timeout].  A query cut by it is undecided, which rejects the
            candidate and learns nothing from that clause while the other
            clauses' counterexamples are still drawn, so it can cost an answer
            (a correct quantified candidate that needs longer to validate is
            proposed again) and never gives a wrong one: [sat] is reported only
            when every query came back unsatisfiable.  Measured on a Rust-derived
            sequence loop, such queries ran 40-136 s each and a 5 s budget on all
            validation queries raised its refutation from 3 of 10 runs to 7 of
            10.  [None] removes the budget. *)
    cex_strategy : cex_strategy; [@default AllExamples]
    check_part_sol_with_lbs : bool; [@default false]
    partial_model_examples : bool; [@default false]
        (** keep as little of a counterexample's model as the clause needs.

            A model assigns a value to every variable its query constrains
            whether or not the constraint forces it, and marks only what it
            chose to mark. This drops the assignments the clause does not use,
            one at a time, keeping a removal only while every example the
            smaller substitution produces is still UNGUARDED — which is the
            whole point and the difference from opening a variable and letting
            the residual become a guard. A guarded example forces nothing until
            its guard is discharged and a guard mentioning a parameter is never
            discharged, so generality bought with a guard is generality the rest
            of the loop cannot act on; generality bought this way leaves the
            example a fact.

            The test is the evaluator, through the guard the example comes out
            with: free, and conservative, since it keeps a variable whenever
            simplification cannot see that the residual is settled. A solver
            asked for validity would drop strictly more and is a change to this
            test rather than to the design. *)
    partial_model_settle_pure : bool; [@default false]
        (** with [partial_model_examples], decide whether a variable may be
            left open by asking the guard discharge (a validity question,
            1 s) whether the clause's predicate-free disjuncts are false for
            every value of the open variables, before the clausal form splits
            them ([ExClauseSet.settle_pure_disjuncts]).  The evaluator alone
            cannot see that [0 <= -1 - x /\ x >= 0] is false, and the clausal
            form makes it two satisfiable guards; a witness's value that the
            clause does not need then stays at the model's point, one new
            example per value.  [false]: the evaluator's test only *)
    partial_model_seq_elements : bool; [@default false]
        (** open, one position at a time, the elements of the sequence literals
            in a counterexample's substitution, keeping an opened element only
            while every example the substitution produces stays UNGUARDED --
            the test [partial_model_examples] keeps a dropped variable by, one
            level finer.  A variable whose value is a sequence can otherwise
            only be kept or dropped whole, so an element the clause never reads
            stays at whatever value the model gave it, and a refutation that
            needs that element at one particular value waits for the model to
            happen to choose it.  Needs [parametric_examples]; independent of
            [partial_model_examples] and applied after it when both are on. *)
    partial_model_seq_elements_goal_only : bool; [@default false]
        (** the same opening, applied only to the examples of a GOAL clause --
            one whose examples have no positive atom, i.e. no head predicate
            application -- and never to a fact or step clause's examples, which
            stay exactly as with the opening off.  Turns the opening on by
            itself (with [parametric_examples]); with it on, the setting of
            [partial_model_seq_elements] does not matter.

            Why only there: resolution binds an example's parameters only by
            syntactic unification, so a positive whose element is a parameter
            no longer meets a step clause's body at the literal the chain
            needs, and the forward positives a refutation walks along are not
            derived. A negative is where the chain ends, so no positive chain
            depends on its elements. Contract as for the opening: every opened
            example is unguarded, and the model's point is an instance of it. *)
    partial_model_group_equal_values : bool; [@default false]
        (** open, as ONE fresh parameter, a group of a counterexample's
            variables the model gave one value (same sort, structurally equal
            value), keeping the replacement only while every example produced
            stays UNGUARDED -- the test [partial_model_examples] keeps a dropped
            variable by. A class is tried whole and, if refused, split into the
            subsets the clause's own equations connect. Dropping one variable at
            a time cannot open two variables a clause equates, since each single
            removal leaves the equation as a guard; opened together the equation
            is settled. Applies to every clause (fact, step, goal), after
            [partial_model_examples] and before the element opening. Needs
            [parametric_examples]. Sound: one parameter for several universally
            quantified clause variables is an instance of the clause's universal
            closure, so an unguarded result is a consequence of the clause, and
            the model's point is an instance of it. *)
        (** When the counterexample's array is CONSTANT, ask again for one that
            is not.

            A learner that reads what an array holds -- a cell abstraction over
            an array-taking predicate -- learns nothing from a constant array:
            it holds the same value at every index, so no example over it can
            distinguish one index from another, and an invariant whose content
            is a relation between indices is unreachable from such data however
            rich the hypothesis space. Measured on an input written for exactly
            that kind of invariant, a quarter of the head examples carried an
            array that varies, against two thirds to five sixths on the inputs
            the method solves.

            A clause of the form "the predicate holds initially" is satisfied by
            any array, so a solver asked for a model may return the cheapest
            one, which is constant. This asks a second time with the array
            required to differ at two concrete indices, and keeps the first
            model whenever the second query is unsatisfiable or undecided, since
            the first is a genuine counterexample and the second is a
            preference.  The condition added is quantifier-free, but that says
            nothing about the query it is added to: when the counterexample
            query already carries a quantifier over array reads, the conjunction
            can fail to return where the query alone did, so a quantified query
            is not re-asked at all.

            Read the scope before relying on it: this addresses only the arrays
            the SOLVER chooses, and on the input it was built for those are the
            minority. The majority come from grounding a parametric example,
            where the array is a universally quantified parameter and the value
            substituted for it is the standard dummy -- which for an array sort
            is a constant array. That one is chosen here rather than by the
            solver, and it is addressed where it is made. *)
    diversify_arrays : bool; [@default false]
    diversify_at_clause_read_indices : bool; [@default false]
        (** Where [diversify_arrays] asks a constant integer-indexed array to
            differ, ask it at the index terms the query itself reads the array
            at, rather than at the fixed indices 0 and 1.  An invariant that
            relates two indices -- [a[k] = b[i+k]] -- is informed only by
            examples whose arrays vary AT those indices; a variation at 0 and 1
            says nothing about it unless the clause happens to read there.  The
            condition is a disjunction over pairs of the read indices, each a
            quantifier-free disequality, so it adds no query shape that might
            not return; with fewer than two read indices it falls back to 0 and
            1.  Off by default.  Measured: the re-ask fires about four times a
            minute on the input it was designed for, whose head examples'
            arrays already vary through the grounding dummy, so where it asks
            the array to vary barely reaches the learner; 21 of 43 answered
            against 23 without it. *)
    diversify_sequences : bool; [@default false]
        (** The sequence counterpart of [diversify_arrays]: when a
            counterexample's model gives a sequence with no position, one
            position, or positions all holding one element, ask again with
            that sequence required to be non-empty and to hold two different
            elements -- at two of the indices the query reads it at when it
            reads it at two or more, at positions 0 and 1 otherwise -- each
            read conjoined with its range premise [0 <= i < seq.len s].  A
            clause that leaves the length open makes a solver return the empty
            sequence, which offers a sequence cell nothing to read.  The same
            policy as the array side: only a quantifier-free query is
            re-asked, with the same budget, and the first model is kept
            whenever the second query does not answer [Sat].  Off by
            default. *)
    record_cell_witnesses : bool; [@default false]
        (** Read the index at which a celled candidate fails out of the
            counterexample's model, and offer it as a candidate cell.

            A celled candidate is read back as
            [\ (a,x..). forall i. phi(i, a[i], x..)], so the query this phase
            poses contains [exists i. not phi] and the model that answers it
            names an index where the candidate is wrong. That index is
            precisely what the abstraction's expansion has no way to guess --
            it offers cells taken from the array instead -- and it is discarded
            here, which is why a loop that is already running the outer half of
            counterexample-guided quantifier instantiation refines by nothing:
            801 counterexamples on one input, 767 of them identical.

            A model reports a value only for a FREE variable, so the
            existential has to be skolemised before the query for the value to
            exist at all. At the occurrences this touches -- positive, with no
            enclosing universal, the clause's own universals being free
            variables of the query rather than binders -- a fresh CONSTANT is
            the whole of skolemisation, and the query is equisatisfiable. A
            constant is also the only form this tree can read back: its model
            reader discards every interpretation of arity greater than zero. *)
    record_head_witnesses : bool; [@default false]
        (** When a clause with a predicate in its head yields a counterexample,
            read out of the model the index at which the candidate's read-back
            [forall j. phi] failed in that head (the existential of its negation,
            skolemised as for [record_cell_witnesses]) and record it beside each
            positive example the counterexample produces, in the side table
            [GoalReads] (its head-witness part), never in the example.

            The synthesizer's celled expansion of that example's head reads it
            ([celled_head_at_witnesses]).  Without it, a positive example over a
            constant array is demanded only at the prefix [0 .. 5], and a
            candidate false only below zero or past the prefix is refuted with
            the same point round after round.  Unlike [record_cell_witnesses],
            whose pool is offered to every atom of every example, the index
            reaches only the example its refutation produced, and only its head.
            Every recorded index is a true index of the example's array, so the
            expansion that offers it states one more consequence of the
            example. *)
    record_goal_reads : bool; [@default true]
        (** When a goal clause -- no predicate in its head -- yields a
            counterexample, record per body atom of the example the indices at
            which the clause reads that atom's arrays, evaluated in the model
            the example is built from, in the side table [GoalReads].

            The synthesizer's cell expansion of a goal example reads the table
            and can put the example's body at exactly those cells.  Without
            them it offers cells guessed from the array (its stored indices,
            their neighbours and a short prefix), and a clause that refutes
            its state at an index outside that guess -- [b[i + k]] with the
            model's [i] in the thousands -- yields a synthesis constraint no
            solution meets.  The index terms are free variables of the
            counterexample query, so their values are already in the model and
            no solver call is added.  The stored example is unchanged: the
            reads ride beside it, never inside the atoms the labeler refutes
            from.  On by default. *)
    generalise_invented_values : bool; [@default false]
        (** when a counterexample's model assigns a variable a numeric value the
            clause itself does not mention, record the example with that
            variable left OPEN -- a parameter guarded by the rest of the premise
            -- instead of at the invented point.

            A model assigns a value to every variable its query constrains
            whether or not the constraint forces it, and marks only what it
            chose to mark, so the unforced values are indistinguishable from the
            ones the problem states. Measured on one run of a Rust-derived
            refutation, a quarter of what this step writes into the examples (96
            of 388 integer occurrences, 15 distinct values including 18623 and
            44363) is a number appearing nowhere in the problem, while the four
            values the problem does state account for the other 292 -- and those
            four are exactly the ones that must stay, being what is proved.

            Leaving a variable open needs no projection to be sound: the pure
            part it stays free in becomes the example's guard, and the other
            variables were substituted rather than eliminated, so their model
            values witness that the clause instance applies wherever the guard
            holds. What is bought is that two examples meaning the same thing
            stop differing by an arbitrary number -- the unrolling of one
            counterexample chain was written as [0,45], [0,29], [0,31], three
            atoms that can never meet -- and can be matched instead.

            Off by default: a generalised example is a STRONGER claim, so it is
            judged on both sides of a tracked pair rather than on a refutation
            alone. *)
    give_up_after_undecided : int option; [@default None]
        (** how many consecutive rounds may end with the candidate rejected and
            nothing learnt -- which is what happens when the solver decides
            neither way about a clause -- before the answer is [unknown].

            [None] is unbounded and is today's behaviour: the round returns a
            VACUOUS counterexample, non-empty so the candidate is rejected and
            saying nothing so the example set does not grow, and the next round
            proposes the same candidate. A correct invariant was rejected on 45
            consecutive iterations that way, on a ten-line satisfiable problem
            whose validation query the solver does not decide over the sequence
            theory.

            The default is unbounded because bounding a loop without measuring
            is how a slow [sat] becomes a [MAYBE]; what is measured so far is
            that the branch is reached on 0 of 69 ordinary files and 28 times in
            30 s on that reproducer, so a bound looks safe, but the default stays
            unbounded until a bound is chosen by measurement. *)
    split_seq_reads : bool; [@default true]
        (** before a validity query is asked, split every read of a
            concatenation by index ([nth (a ++ b) j] becomes an [ite] over
            whether [j] falls in [a] or in [b]) -- an identity in every model,
            so the question asked is the same one.  A candidate read back from
            sequence cells is a universal over a sequence's positions, and the
            clause it is checked against reads a sequence built by
            concatenation; with the read left whole, z3 was observed not to
            answer such a query in 20 s where the split form is decided at
            once. *)
    instantiate_readback_universals : bool; [@default false]
        (** before asking whether a candidate violates a clause that reads a
            sequence under a quantifier, try to show the clause valid by a
            STRENGTHENING that binds nothing: a universal of a premise --
            which a candidate read back from sequence cells puts there, one
            per sequence, over its positions -- replaced by its instances at
            the positions the clause reads and at the values its case splits
            single out, and a universal of the conclusion by a fresh
            variable.  Each such form implies the clause, so only its
            validity is read: it ends the check with no counterexample, and
            any other answer leaves the question to the unrewritten query,
            which alone produces counterexamples.  A clause composing three
            such sequences was not decided by that query in minutes, while
            its instances are quantifier-free.  When off, only the
            unrewritten query is asked. *)
    retry_undecided_readback_forms : bool; [@default false]
        (** with [instantiate_readback_universals], ask an instantiated form
            that Z3's default strategy left undecided once more, under the
            tactic [(then simplify der qe-light simplify smt)]
            ([Z3interface.check_sat_by_elimination]), whose steps are each an
            equivalence, and read only an [unsat] (the form valid).  A form is
            quantifier-free and binds no sequence, yet on Z3 5.1.0 the default
            strategy was observed to time out at 20 s on the negation of a
            composition form -- [t = store s i 0], [u = store t i 0] and cell
            conditions over two positions, 4.15.2 deciding it in under a
            second -- while the explicit tactic decided it in 0.2 s on both
            versions.  Only a proof is taken from the retry, so the switch can
            only turn an undecided form into a proved one.  When off, an
            undecided form stays undecided. *)
    readback_subst_definitions : bool; [@default false]
        (** with [instantiate_readback_universals], ask each instantiated form
            with the variables its top-level disequations define substituted
            away and the result simplified (an identity for validity), so
            that the simplifier's store rules can close what the form states
            about composed writes.  A composition clause over three sequences,
            whose form Z3 4.15.2 decided in 0.2 s, was not decided by Z3 5.1.0
            in 20 s; its substituted form is decided by the simplifier.  When
            off, the forms are asked as they are built. *)
    fork_unreturnable_queries : bool; [@default true]
        (** ask a counterexample query that binds a sequence under a
            quantifier ([may_not_return]) in a forked copy of the process,
            killed when the query's budget runs out ([smt_timeout_quantified],
            10 s when no budget is set).  Z3's own budget does not hold on such
            a query: one was observed still running minutes into a 5 s budget,
            inside the sequence theory, which stopped the whole run in this
            phase.  An answer the copy sends back is the answer the pooled
            solver would give, since the copy holds the same solver state; a
            copy that runs out of time leaves the clause undecided, which
            rejects the candidate and learns nothing from the clause, as a
            timeout does.  So the switch changes only how long an undecided
            query can take.  On by default.  When off, such a query is asked
            in-process. *)
    fork_quantified_queries : bool; [@default false]
        (** with [fork_unreturnable_queries], ask in a killed copy every
            counterexample query that still holds a quantifier, not only the
            shapes [may_not_return] refuses.  The copy's answer is the pooled
            solver's; what changes is that a query that answers only after its
            budget is cut off at it (in this process Z3 overran a 5 s budget
            to 8.6 s on such questions), and that the memory a question takes
            is the copy's and is given back when it exits: on a Rust-derived
            input the process grew from 1.1 to 2.9 GB resident within 30 s
            while one quantified question was asked in its pooled context,
            where the same question alone in z3 answered [unknown] in 0.9 s
            at 51 MB.  A satisfiable answer is asked again here for its model, as
            for the refused shapes.  When off, only the refused shapes are
            forked. *)
    scoped_first_quantified_validation : bool; [@default false]
        (** ask a quantified counterexample query that is asked in this
            process first with its negated clause inside a scope of the
            pooled solver ([Z3interface.check_sat_scoped_first]), under
            [scoped_first_quantified_validation_ms], and only when that leaves
            it undecided, as it is asked without the switch (then the
            sequence-axiom fallback as before).  Unscoped, Z3 answers such a
            query in a pushed context with its bare [smt] tactic; scoped, with
            its incremental core, which decided validation questions over
            sequences and datatypes in 0.1 s that the tactic left undecided at
            5 s, and leaves others undecided that the tactic decides, which is
            why it comes first and short.  Its [unsat] and [sat] are read as
            the unscoped ask's are.  Not applied to a shape [may_not_return]
            refuses nor to a query asked in a forked copy.  Off by default. *)
    scoped_first_quantified_validation_ms : int; [@default 1000]
        (** the scoped ask's budget, in ms, capped by the query's own *)
    fresh_context_quantified_queries : bool; [@default false]
        (** ask a counterexample query that holds a quantifier, when it is
            asked in this process, as the process-wide [AlwaysFresh] policy of
            PCSat's [z3_fresh_retry] asks every quantified query, but for this
            phase only: in a Z3 context of its own, in negation normal form,
            with the definitions it reaches ([Z3interface.check_sat_fresh]; a
            reset clean context when [z3_clean_reset_pool] is on), instead of
            first in the pooled context every other query shares and, when
            that answers [unknown], again in a context of its own (the default
            [RetryOnUnknown]).  A shape that check refuses ([may_not_return])
            is asked in the pooled context as before.  The question is the same
            (negation normal form is an equivalence), so a decided answer means
            the same; which questions are decided within the budget can
            differ.  Off by default. *)
    fork_unreturnable_kill_ms : int option; [@default None]
        (** with [fork_unreturnable_queries], the wall-clock budget after which
            the forked copy is killed, in ms; the larger of this and the
            query's own budget is used ([ForkedQuery.kill_ms]), so a copy is
            never killed earlier than without the field.  Why: a query of the
            refused shape that answers after its budget is waited for when
            asked in-process (Z3's budget does not hold there), but was cut off
            at the budget in the copy, which left its clause undecided and
            learned nothing from it; two Rust-derived inputs answered 5-6 times
            of 6 in-process lost their answers that way.  A copy's answer is
            still the pooled solver's, so the field changes only how long a
            refused query may take before it is undecided.  Not applied inside
            the Houdini pre-pass, whose budget is the window's remainder.
            [None]: killed at the query's budget. *)
    weaken_unreturnable_queries : bool; [@default false]
        (** before a counterexample query that [may_not_return] refuses is
            asked, ask it without its top-level conjuncts that the refusal is
            about (typically a premise the clause states as a universal over
            sequences: a law inlined from a callee's postcondition).  The rest
            is implied by the query, so [unsat] there is the query's answer.
            A model of the rest is kept only when every dropped conjunct is
            shown to hold under it -- its negation, with the model's values
            substituted, asked in a forked copy killed at the query's budget,
            must be unsatisfiable, so it holds for every value of whatever the
            model left unassigned -- and is then a model of the whole query.
            Any other outcome leaves the query to the path it takes with the
            switch off.  A clause whose query z3 did not answer in minutes,
            because the sequence universal has to be shown to hold in the model
            being built, was decided this way in well under a second: the rest
            at once, and each dropped law, once the model's values are in it,
            by an existential question over a sequence that z3 refutes by
            instantiating the law's own index universal. *)
    houdini_weaken_unreturnable : bool; [@default true]
        (** inside the Houdini pre-pass's window only, ask a question that
            [may_not_return] refuses as [weaken_unreturnable_queries] does
            (the rest first; its [unsat] is the answer, a model of it only
            when every dropped conjunct is shown to hold under it) before it
            is asked in a killed copy.  The pre-pass asks one question per
            (clause, candidate), and a loop clause carrying a callee's law as
            a universal over sequences makes each of them such a question:
            one input lost about forty of them, trivial ones such as
            [len v >= 0] among them, to the copy's 5 s kill, and the
            pre-pass spent its budget before reaching a fixed point.  The
            weakened question is implied by the original, so this adds
            answers and never changes one.  On by default. *)
    weaken_unreturnable_keep_cells : bool; [@default false]
        (** with [weaken_unreturnable_queries], keep asking a truth-table cell
            whose validity question [may_not_return] refuses, instead of
            leaving it undecided ([WeakenedQuery.leaves_cells_undecided]).  The
            validator's weakening and the guard discharge in a copy are
            unchanged; only the truth table's side effect is dropped.  Why: a
            cell left undecided is a qualifier the labeling cannot use, and
            the cells of the refused shape that answer in-process, slowly, are
            what two Rust-derived inputs answered 5-6 times of 6 without the
            weakening needed.  Such a cell is asked in-process, with no budget
            unless the truth table has one, so it can fail to return: the risk
            the side effect guards against is taken back.  Off: the cells are
            left undecided whenever the weakening is on. *)
    record_premise_instances : bool; [@default false]
        (** carry a premise the clause states with a quantifier into the
            examples derived from it, instantiated at the counterexample's own
            terms. Synthesis learns only from examples and an example is two
            sets of atoms, so a premise the clause states is invisible to it:
            the candidate is asked to satisfy the examples everywhere, not only
            where the premise holds, and Validation then rejects it for a
            situation the premise excludes. *)
    arrays_as_functions : bool; [@default true]
    array_pointwise_elim : bool; [@default true]
        (** ask a counterexample query whose integer arrays are constrained
            only cell by cell -- read at ground indices and at the variable of
            a top-level universal -- with those arrays eliminated
            ([Ast.ArrayPointwise]: an equisatisfiable rewrite whose models
            read back to the query's), before asking it as before *)
        (** ask a counterexample query that reads its arrays only through
            [select] with each array an uninterpreted function, and read the
            function the model gives back as an array term.

            The two questions are equisatisfiable on that fragment: an array
            model gives a function model ([f := fun x -> select a x]), so the
            function query's [unsat] is the array query's [unsat] in every
            model of the array theory; and a function model is an array model
            in the standard structure, where every function is an array, which
            is a countermodel, and one countermodel refutes a candidate.  A
            read of a write is first rewritten by read over write, which is
            exact.  What is bought is a decision: a candidate stating a
            universal over the cells of two arrays yields step and goal
            queries Z3 did not decide as arrays in 11 s, 8 of 8, and decided
            as functions in at most 0.1 s, never disagreeing where both
            decided.  An undecided function query, and any query outside the
            fragment (a write whose result is not only read, an array
            equality, an array under a binder, an array literal, an array
            inside a tuple), is asked as without it.  A query the forked, killed
            copy would take ([fork_unreturnable_queries] with a shape that may
            not return) still goes there: the translation is never a reason to
            ask such a query in this process.  On by default. *)
    diversify_scalar_counterexamples : bool; [@default false]
        (** when a counterexample's integer variables lie within a Manhattan
            distance [m] of the last counterexample returned for the same
            variables, ask the same query again with the distance required,
            keeping the first model unless the second query answers [Sat];
            [m] starts at 4, doubles on success and halves (not below 1) on
            failure (the cooperative verifier of Batz et al., TACAS 2023).
            A solver returns the cheapest model, so the integers of the
            examples cluster at a few small values (on a loop bounded by
            [1 <= S], S is 1 or 2 in every example), and at those values the
            general bounds of an invariant coincide with literals about the
            examples' constants, which the synthesizer then has no reason to
            avoid.  It only chooses which counterexample is used, so it cannot
            change a verdict.  Off by default. *)
    fact_clause_examples : bool; [@default false]
        (** when a candidate violates a FACT clause -- no predicate in its
            premise, exactly one in its head -- record the clause itself as an
            example too, a positive whose parameters are all the clause's
            variables and whose guard is its premise, beside the model's point.

            The clause says the atom holds for every value of its variables,
            and the model's point is one of them, chosen by the solver: for an
            array that is typically a constant, and the value it holds is
            whatever the solver found cheapest.  A candidate that bounds array
            contents by a constant then fits every point it is shown and is
            refuted one invented constant at a time, which is a way for a
            quantified invariant never to be reached.  The clause is exact --
            it is the constraint -- so recording it loses nothing and asserts
            nothing the problem does not, and the synthesis phase grounds its
            parameters as it grounds any parametric example. *)
    partial_model_fact_examples : bool; [@default false]
        (** when a candidate violates a FACT clause, keep BESIDE the model's
            point its maximally partial form: the point with every assignment
            dropped that the clause's pure part does not need, one at a time,
            each kept dropped only while the example stays unguarded (the
            test of [partial_model_examples], applied to fact clauses and
            added rather than substituted).

            What it buys is a positive the resolver can use.  The resolver
            proves a head atom by resolving it through a clause and matching
            the body atoms against the decided positives; a guarded positive
            is not matched, and a ground one matches only its own values.  The
            model's values at the positions the fact does not constrain (a
            prophecy, the final value of a borrow) are whatever the candidate
            made the solver pick, so a forward step whose predecessor needs
            one particular value there is provable only once some round's
            model happened to pick it.  The partial form is unguarded and open
            at exactly those positions.  It is the constraint instantiated
            where its premise is settled, so it asserts nothing the problem
            does not; with [partial_model_examples] on it adds nothing. *)
  }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let instantiate_ext_files cfg =
    let open Or_error in
    (match cfg.houdini_extracted_qualifiers with
    | None -> Ok None
    | Some f -> Qualifier.Generator.Config.load_ext_file f >>| Option.some)
    >>= fun houdini_extracted_qualifiers ->
    Ok { cfg with houdini_extracted_qualifiers }

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "Validator"
    let instantiate = instantiate_ext_files
  end)
end

(* The candidate atoms of the Houdini-style pre-pass for one unknown, over its
   parameters [params]: the declared ones as they are and in their order, then
   the generated ones that can be candidates at all ([usable]), without
   repetition (by printed form, a declared atom included), the smallest by
   [Formula.ast_size] first with ties broken by printed form, so the result is
   a function of the two lists as sets and not of their order, filling up to
   [cap] atoms in all.  The declared atoms are never dropped, even past [cap]:
   the input asked for them. *)
module HoudiniCandidates = struct
  (* a formula whose free variables are all among [params], with no unknown,
     that is not a Boolean literal: an atom a conjunction over the unknown's
     parameters can carry.  A qualifier over a template's cell column, or an
     atom of a definition body taken from under its binder, has a free
     variable of its own and is refused.  A quantified formula over the
     parameters is kept: the extraction lifts a clause's bounded universal
     premises into such qualifiers ([forall k. 0 <= k < len v => R(v[k])]),
     which are exactly the contract facts a declared list states, and the
     pre-pass's questions carry them as they carry a declared one.

     With [dtenv] (the datatypes the problem itself uses), a formula is also
     refused when a datatype it mentions has a definition different from the
     problem's under the same name.  The atoms of the input's definitions are
     read from the process-global definitions, which are over the sorts the
     input declared; inside the solve of a finite instance, where a quantified
     sort is replaced by an enumeration, the same datatype name is defined over
     the enumeration, and an atom mixing the two made the solver's datatype
     conversion raise. *)
  let agrees dtenv phi =
    Map.Poly.is_empty dtenv
    ||
    match Map.force_merge dtenv (DTEnv.of_formula phi) with
    | _ -> true
    | exception exn_ when not (Common.Timer.is_async exn_) -> false

  (* a literal, or a quantifier over one ([forall x. true]), which a
     normalisation that simplifies the body but keeps the binder leaves *)
  let rec literal = function
    | Formula.Bind (_, _, body, _) -> literal body
    | phi -> Formula.is_true phi || Formula.is_false phi

  let usable ?(dtenv = Map.Poly.empty) (params : sort_env_list) phi =
    let names = Set.Poly.of_list (List.map params ~f:fst) in
    agrees dtenv phi
    && Set.is_empty (Formula.pvs_of phi)
    && Set.is_subset (Formula.tvs_of phi) ~of_:names
    && not (literal phi)

  (* each atom and its negation: a template hole may take a qualifier in
     either polarity, and a conjunction only in the one it is given *)
  let both_polarities phis =
    List.concat_map phis ~f:(fun phi -> [ phi; Evaluator.simplify_neg phi ])

  (* Whether [phi], read as a validity question, binds a variable of
     sequence sort existentially: under an [exists] at positive polarity or a
     [forall] at negative polarity.  An implication's premise and a negation
     flip the polarity; any other connective keeps it, and a binder nested in
     an atom (a formula embedded in a term) is not seen, so the answer can
     only be [false] where it might have been [true].  With [arrays], a
     variable of an [Int]-indexed array sort counts as a sequence (the
     array-plus-length encoding of one); without it, exactly as before. *)
  let binds_sequence_existentially ?(arrays = false) phi =
    let has_seq = List.exists ~f:(fun (_, s) ->
        match s with
        | T_seq.SSeq _ -> true
        | T_array.SArray (si, _) -> arrays && Term.is_int_sort si
        | _ -> false)
    in
    let rec go ~pos = function
      | Formula.Bind (b, senv, body, _) ->
          (match (b, pos) with
          | Formula.Exists, true | Formula.Forall, false -> has_seq senv
          | _ -> false)
          || go ~pos body
      | Formula.UnaryOp (Formula.Not, p, _) -> go ~pos:(not pos) p
      | Formula.BinaryOp ((Formula.And | Formula.Or), p, q, _) ->
          go ~pos p || go ~pos q
      | Formula.BinaryOp (Formula.Imply, p, q, _) ->
          go ~pos:(not pos) p || go ~pos q
      | Formula.BinaryOp (Formula.Iff, p, q, _)
      | Formula.BinaryOp (Formula.Xor, p, q, _) ->
          go ~pos p || go ~pos:(not pos) p || go ~pos q || go ~pos:(not pos) q
      | Formula.LetFormula (_, _, _, body, _) -> go ~pos body
      | _ -> false
    in
    go ~pos:true phi

  (* With [quota > 0] the quantified generated atoms are ranked apart from
     the quantifier-free ones: at most [quota] of them are kept, the smallest
     first, and they do not count against [cap], which then bounds the
     declared and the quantifier-free generated atoms together.  A quantified
     atom is larger than the quantifier-free ones over the same terms, so a
     single ranking by size keeps it last and a cap cuts it first, while it is
     the kind of fact (a contract's pointwise postcondition) a loop invariant
     most often needs.  [quota = 0] is the single ranking. *)
  (* the usable atoms of [phis], keyed by printed form, without repetition,
     the smallest by [Formula.ast_size] first, ties by printed form, minus
     those whose printed form is in [seen] *)
  let ranked ~dtenv ~params ~seen phis =
    List.filter_map phis ~f:(fun phi ->
        if usable ~dtenv params phi then Some (Formula.str_of phi, phi)
        else None)
    |> List.dedup_and_sort ~compare:(fun (s1, p1) (s2, p2) ->
           match Int.compare (Formula.ast_size p1) (Formula.ast_size p2) with
           | 0 -> String.compare s1 s2
           | c -> c)
    |> List.filter ~f:(fun (str, _) -> not (Hash_set.mem seen str))

  (* With [inclusion_quota > 0], the atoms of [inclusions] (the relation
     inclusions) have a quota of their own, outside both [cap] and [quota]:
     the result is exactly the merge of [declared] and [generated] as if
     [inclusions] were empty, followed by at most [inclusion_quota] of the
     usable inclusion atoms not already in it, the smallest first.  So
     switching the family on can only add atoms, never displace one the
     other families keep -- an inclusion is a small quantified formula, and
     ranked with the other quantified atoms it took the whole of [quota]
     ahead of the contract's pointwise facts.  [inclusion_quota = 0] merges
     [inclusions] into [generated], the ranking of before. *)
  (* [affine_quota] and [affine] are the same for the affine element
     universals, and [counting_quota] and [counting] for the length sums,
     three-term equations and guarded orders: with several quotas positive,
     the inclusions come first, then the affine atoms, then the counting
     atoms, each deduplicated against everything before *)
  let merge ?(quota = 0) ?(inclusion_quota = 0) ?(inclusions = [])
      ?(affine_quota = 0) ?(affine = []) ?(counting_quota = 0) ?(counting = []) ?(own_quotas = [])
      ~dtenv ~cap ~(params : sort_env_list) ~(declared : Formula.t list)
      ~(generated : Formula.t list) () =
    let own =
      [
        (inclusion_quota, inclusions);
        (affine_quota, affine);
        (counting_quota, counting);
      ]
    in
    let generated =
      generated
      @ List.concat_map own ~f:(fun (q, atoms) -> if q <= 0 then atoms else [])
    in
    let seen = Hash_set.create (module String) in
    List.iter declared ~f:(fun phi -> Hash_set.add seen (Formula.str_of phi));
    let fresh = ranked ~dtenv ~params ~seen generated in
    let room = max 0 (cap - List.length declared) in
    let kept =
      if quota <= 0 then declared @ List.map ~f:snd (List.take fresh room)
      else
        let qf, quant =
          List.partition_tf fresh ~f:(fun (_, phi) ->
              Formula.is_quantifier_free phi)
        in
        declared
        @ List.map ~f:snd (List.take qf room)
        @ List.map ~f:snd (List.take quant quota)
    in
    let kept =
      List.fold own ~init:kept ~f:(fun kept (q, atoms) ->
          if q <= 0 then kept
          else (
            List.iter kept ~f:(fun phi -> Hash_set.add seen (Formula.str_of phi));
            kept @ List.map ~f:snd (List.take (ranked ~dtenv ~params ~seen atoms) q)))
    in
    (* each family of [own_quotas] after everything above, in order, at most
       its quota of its usable atoms not already kept, in the order given
       (not re-ranked by size: a family whose atoms are all of one size is
       ordered by its own generator) *)
    List.fold own_quotas ~init:kept ~f:(fun kept (atoms, q) ->
        List.iter kept ~f:(fun phi -> Hash_set.add seen (Formula.str_of phi));
        let fresh =
          List.filter atoms ~f:(fun phi ->
              usable ~dtenv params phi
              && not (Hash_set.mem seen (Formula.str_of phi)))
        in
        kept @ List.take fresh (max 0 q))

  (* {2 Generated classes}

     Nine families of atoms over an unknown's parameters [params], each
     bounded by its own [limit] ([limit <= 0] gives none) and each a function
     of the parameters' names and sorts (and, for the memberships, the
     quantified facts and the inclusions, of the given definitions and
     formulas) only -- never of examples, a model or the
     synthesizer's state.  They are candidates for the pre-pass and nothing
     else: an atom that is not inductive is dropped by the pre-pass's own
     questions, so a family can only cost questions and never an answer.

     The terms an unknown "reaches" are its parameters and their projections
     through the selectors of single-constructor datatypes, at most two
     selectors deep ([CellQual.terms_of_sort ~depth:2]); two is the depth at
     which the Rust-derived inputs keep an iterator's position
     ([tuple_proj.1 (mut_current it)]), and each further level multiplies the
     terms of a record-heavy signature. *)

  let reach_depth = 2

  (* A generator given [stop] asks it once per atom it builds or normalises
     and raises [Budget_spent] once it holds: a family over a record-heavy
     signature builds thousands of atoms, and the pre-pass's budget covers
     the time spent building them. *)
  exception Budget_spent

  let poll stop = if stop () then raise Budget_spent

  (* The pre-pass in one or two rounds.  [round ~inclusions ~budget_ms] runs
     one whole pre-pass (candidates, fixed point, final check) with or
     without the inclusion family, under the given budget, and gives its
     outcome.  With [second_round] false it is called once, with the
     inclusions and [budget_ms] -- the one-round pre-pass.  With
     [second_round] true it is called first without the inclusions under
     [budget_ms]; a [`Solution] or [`Not_applicable] (nothing to try, or a
     spent budget) is the outcome, and only a [`Counterexamples] (a fixed
     point the final check rejected) calls it a second time, with the
     inclusions, under [round_budget_ms] when given and [budget_ms]
     otherwise, whose outcome is returned in place of the first.  So [round]
     is called at most twice and at most once without the inclusions. *)
  let rounds ~second_round ~budget_ms ~round_budget_ms ~round =
    if not second_round then round ~inclusions:true ~budget_ms
    else
      match round ~inclusions:false ~budget_ms with
      | `Counterexamples _ ->
          round ~inclusions:true
            ~budget_ms:
              (match round_budget_ms with Some _ -> round_budget_ms | None -> budget_ms)
      | (`Solution _ | `Not_applicable) as outcome -> outcome

  (* the sorts reachable from [s] through single-constructor selectors, [s]
     itself included, to [depth] *)
  let rec reached_sorts depth s =
    s
    ::
    (match s with
    | T_dt.SDT dt when depth > 0 -> (
        match Datatype.conses_of dt with
        | [ cons ] ->
            List.concat_map (Datatype.sels_of_cons cons) ~f:(fun sel ->
                reached_sorts (depth - 1) (Datatype.sort_of_sel dt sel))
        | _ -> [])
    | _ -> [])

  (* every reached term, with the position of the parameter it starts at, in
     parameter order, each parameter's terms by printed sort and then printed
     term *)
  let reached (params : sort_env_list) : (int * Term.t) list =
    List.concat_mapi params ~f:(fun i (x, s) ->
        let arg = [ (Term.mk_var x s, s) ] in
        reached_sorts reach_depth s
        |> List.dedup_and_sort ~compare:(fun a b ->
               String.compare (Term.str_of_sort a) (Term.str_of_sort b))
        |> List.concat_map ~f:(fun so ->
               List.map (CellQual.terms_of_sort ~depth:reach_depth so arg)
                 ~f:(fun t -> (i, t))))

  (* the terms of sort [s] reached from all of [params] *)
  let reached_of_sort (params : sort_env_list) s =
    CellQual.terms_of_sort ~depth:reach_depth s
      (List.map params ~f:(fun (x, s) -> (Term.mk_var x s, s)))

  (* the first [n] tuples of the product of [cands], lexicographically: the
     enumeration is bounded by [n] tuples however many columns there are *)
  let rec tuples n = function
    | [] -> [ [] ]
    | c :: cs ->
        let rest = tuples n cs in
        List.take
          (List.concat_map c ~f:(fun t -> List.map rest ~f:(fun r -> t :: r)))
          n

  (* the normal form the families are deduplicated in and a declared atom is
     compared in: simplified, normalised, simplified *)
  let normal phi = Evaluator.(simplify >> Normalizer.normalize >> simplify) phi

  (* [atoms] without literals and repetitions (by the printed normal form),
     the smallest by [Formula.ast_size] first, ties by printed form, at most
     [limit]: the bound keeps the simplest atoms, and the result does not
     depend on the order the atoms were produced in *)
  let smallest ?(stop = fun () -> false) ~limit atoms =
    List.filter_map atoms ~f:(fun phi ->
        poll stop;
        let phi = normal phi in
        if literal phi then None else Some (Formula.str_of phi, phi))
    |> List.dedup_and_sort ~compare:(fun (s1, p1) (s2, p2) ->
           match Int.compare (Formula.ast_size p1) (Formula.ast_size p2) with
           | 0 -> String.compare s1 s2
           | c -> c)
    |> Fn.flip List.take (max 0 limit)
    |> List.map ~f:snd

  (* a sort an equation between two reached terms may be over: not a
     Boolean (a Boolean term's equation is an iff, which the membership
     family states directly) and not an array (an equation between two
     arrays is extensional, a question the solver often leaves undecided) *)
  let equatable s = not (Term.is_bool_sort s || Term.is_array_sort s)

  (* [t1 = t2] for reached terms [t1], [t2] of one sort starting at two
     different parameters: the frame conditions a loop keeps between its
     entry values and its current ones ([mut_final it = mut_final e],
     [it.1 = en]).  Two terms of one parameter are left out: they state a
     fact about one value, which the other families and the extraction
     cover. *)
  let frame_equations ?(stop = fun () -> false) ~limit (params : sort_env_list)
      =
    if limit <= 0 then []
    else
      let ts =
        List.filter (reached params) ~f:(fun (_, t) ->
            equatable (Term.sort_of t))
      in
      smallest ~stop ~limit
      @@ List.concat_map ts ~f:(fun (i1, t1) ->
             List.filter_map ts ~f:(fun (i2, t2) ->
                 poll stop;
                 if
                   i1 < i2
                   && String.equal
                        (Term.str_of_sort (Term.sort_of t1))
                        (Term.str_of_sort (Term.sort_of t2))
                 then Some (Formula.eq t1 t2)
                 else None))

  (* [t = c(u1, ..., un)] for [c] the one constructor of [t]'s sort: a
     conjunction of field equations the frame family states field by field *)
  let single_cons_eq q =
    Formula.is_eq q
    &&
    let t1, t2, _ = Formula.let_eq q in
    List.exists [ t1; t2 ] ~f:(fun t ->
        T_dt.is_cons t
        &&
        match Term.sort_of t with
        | T_dt.SDT dt -> List.length (Datatype.conses_of dt) = 1
        | _ -> false)

  (* the memberships of reached terms in the relations the unknown carries
     and in the input's Boolean definitions: [r[t1]...[tk] = true] for a
     reached term [r] whose sort is an array (curried to any depth) ending in
     [Bool] -- a contract predicate the unknown depends on, such as
     [q_invariant] or [q_produces] -- and [d(t1, ..., tk)], the definition's
     body instantiated, for a non-recursive Bool-valued definition of [defs];
     each index or formal of sort [s] filled by the terms of sort [s] reached
     from all of [params], at most [limit] tuples per relation or definition,
     and at most [limit] atoms in all.  A definition none of whose formals'
     sorts is reached is skipped; an instance that is a literal or a
     constructor equation of a single-constructor datatype is dropped. *)
  let memberships ?(stop = fun () -> false) ~limit ~(defs : FunEnv.t)
      (params : sort_env_list) =
    if limit <= 0 then []
    else
      let pset = Set.Poly.of_list (List.map params ~f:fst) in
      let over_params q = Set.is_subset (Formula.tvs_of q) ~of_:pset in
      let rels =
        List.concat_map (reached params) ~f:(fun (_, r) ->
            match CellQual.uncurry_array_sort (Term.sort_of r) with
            | (_ :: _ as idx), e when Term.is_bool_sort e ->
                let cands = List.map idx ~f:(reached_of_sort params) in
                if List.exists cands ~f:List.is_empty then []
                else
                  List.map (tuples limit cands) ~f:(fun ts ->
                      Formula.eq (T_array.mk_select_app r ts)
                        (T_bool.mk_true ()))
            | _ -> [])
      in
      let defined =
        Map.Poly.to_alist defs
        |> List.concat_map ~f:(fun (_, (fargs, sret, body, isrec, _)) ->
               if isrec || (not (Term.is_bool_sort sret)) || List.is_empty fargs
               then []
               else
                 let cands =
                   List.map fargs ~f:(fun (_, s) -> reached_of_sort params s)
                 in
                 if List.exists cands ~f:List.is_empty then []
                 else
                   let body = Formula.of_bool_term body in
                   List.filter_map (tuples limit cands) ~f:(fun ts ->
                       poll stop;
                       let sub =
                         Map.Poly.of_alist_exn
                           (List.zip_exn (List.map fargs ~f:fst) ts)
                       in
                       let q = Evaluator.simplify (Formula.subst sub body) in
                       if single_cons_eq q || not (over_params q) then None
                       else Some q))
      in
      smallest ~stop ~limit (rels @ defined)

  (* the integer terms an unknown reaches: the reached integer terms and the
     lengths of the reached sequences *)
  let int_terms (params : sort_env_list) =
    let ts = List.map (reached params) ~f:snd in
    List.filter ts ~f:(fun t -> Term.is_int_sort (Term.sort_of t))
    @ List.filter_map ts ~f:(fun t ->
          match Term.sort_of t with
          | T_seq.SSeq se -> Some (T_seq.mk_len se t)
          | _ -> None)

  (* the existential memberships of the relations an unknown carries, for a
     relation [r] (a reached term whose sort is an array, curried to any
     depth, ending in [Bool]) exactly one of whose index sorts no reached term
     has, and that sort a sequence sort: [exists t. r[t1]..[t]..[tk] = true]
     and [exists t. r[..t..] = true /\ len t + x = y] for integer terms [x],
     [y] the unknown reaches ([int_terms]).  The other indices are filled by
     reached terms rooted at pairwise different parameters, and [x] and [y]
     are rooted at different parameters: the shape of a loop's history
     between its entry state and its current one ([exists t. len t + n =
     e.1 /\ produces(e.0, t, s.0)]), which keeps the family to a few dozen
     atoms on a record-heavy signature.

     Contract: [limit <= 0] gives [[]]; otherwise at most [limit] atoms, the
     plain memberships first and then the length ones, each group in the
     order the terms are reached, without repetition by printed form; every
     atom is an existential over one fresh sequence variable whose free
     variables are among [params] (the bound name is chosen apart from
     [params]); a relation with no unreached index sort, or with two or
     more, or whose one unreached sort is not a sequence, gives nothing.
     With [array_pairs], a single-constructor datatype of exactly an
     [Int]-indexed array and an [Int] also counts as a sequence: the
     existential then binds two fresh variables, the value is the
     constructor over them and its length the [Int] one; without it the
     result is the one before the option existed.  A function of [params]'
     names and sorts only. *)
  let exists_memberships ?(stop = fun () -> false) ?(array_pairs = false)
      ~limit (params : sort_env_list) =
    if limit <= 0 then []
    else
      let pset = Set.Poly.of_list (List.map params ~f:fst) in
      let rec pick name =
        if Set.mem pset (Ident.Tvar name) then pick (name ^ "_")
        else Ident.Tvar name
      in
      let tvar = pick "hext" in
      let avar = pick "hexa" and lvar = pick "hexl" in
      (* the history as a fresh value of the unreached index sort: its
         binders, the value itself and its length.  A sequence is one bound
         variable.  With [array_pairs], a single-constructor datatype of
         exactly two fields, an [Int]-indexed array and an [Int] (the
         array-plus-length encoding of a sequence), is the constructor over
         two bound variables, its length the [Int] one. *)
      let history_of = function
        | T_seq.SSeq se as sq ->
            let tv = Term.mk_var tvar sq in
            Some ([ (tvar, sq) ], tv, T_seq.mk_len se tv)
        | T_dt.SDT dt when array_pairs -> (
            match Datatype.conses_of dt with
            | [ cons ] -> (
                let fields =
                  List.map (Datatype.sels_of_cons cons) ~f:(fun sel ->
                      Datatype.sort_of_sel dt sel)
                in
                let int_indexed = function
                  | T_array.SArray (si, _) -> Term.is_int_sort si
                  | _ -> false
                in
                let arr s = (avar, s) and len = (lvar, T_int.SInt) in
                let mk binders =
                  let args =
                    List.map binders ~f:(fun (x, s) -> Term.mk_var x s)
                  in
                  Some
                    ( binders,
                      T_dt.mk_cons dt (Datatype.name_of_cons cons) args,
                      Term.mk_var lvar T_int.SInt )
                in
                match fields with
                | [ sa; si ] when int_indexed sa && Term.is_int_sort si ->
                    mk [ arr sa; len ]
                | [ si; sa ] when int_indexed sa && Term.is_int_sort si ->
                    mk [ len; arr sa ]
                | _ -> None)
            | _ -> None)
        | _ -> None
      in
      let rooted = reached params in
      let rooted_of_sort s =
        List.filter rooted ~f:(fun (_, t) ->
            String.equal
              (Term.str_of_sort (Term.sort_of t))
              (Term.str_of_sort s))
      in
      let ints =
        List.concat_mapi params ~f:(fun i (x, s) ->
            List.map (int_terms [ (x, s) ]) ~f:(fun t -> (i, t)))
      in
      let pairs =
        List.concat_map ints ~f:(fun (i1, x) ->
            List.filter_map ints ~f:(fun (i2, y) ->
                if i1 <> i2 then Some (x, y) else None))
      in
      let plain, lengths =
        List.unzip
        @@ List.concat_map rooted ~f:(fun (_, r) ->
               match CellQual.uncurry_array_sort (Term.sort_of r) with
               | (_ :: _ as idx), e when Term.is_bool_sort e -> (
                   let cands = List.map idx ~f:rooted_of_sort in
                   match
                     List.filter_mapi cands ~f:(fun k c ->
                         if List.is_empty c then Some k else None)
                   with
                   | [ k ] -> (
                       match history_of (List.nth_exn idx k) with
                       | Some (binders, tv, tlen) ->
                           let others =
                             List.filteri cands ~f:(fun j _ -> j <> k)
                           in
                           let rec fill = function
                             | [] -> [ [] ]
                             | c :: cs ->
                                 let rest = fill cs in
                                 List.concat_map c ~f:(fun (i, t) ->
                                     List.filter_map rest ~f:(fun r ->
                                         if
                                           List.exists r ~f:(fun (i', _) ->
                                               i = i')
                                         then None
                                         else Some ((i, t) :: r)))
                           in
                           List.map (List.take (fill others) limit)
                             ~f:(fun ts ->
                               poll stop;
                               let ts = List.map ts ~f:snd in
                               let args =
                                 List.take ts k @ (tv :: List.drop ts k)
                               in
                               let mem =
                                 Formula.eq
                                   (T_array.mk_select_app r args)
                                   (T_bool.mk_true ())
                               in
                               ( Formula.exists binders mem,
                                 List.map pairs ~f:(fun (x, y) ->
                                     Formula.exists binders
                                       (Formula.mk_and mem
                                          (Formula.eq (T_int.mk_add tlen x) y)))
                               ))
                       | None -> [])
                   | _ -> [])
               | _ -> [])
      in
      let seen = Hash_set.create (module String) in
      List.filter (plain @ List.concat lengths) ~f:(fun phi ->
          let key = Formula.str_of phi in
          if Hash_set.mem seen key then false
          else (
            Hash_set.add seen key;
            true))
      |> Fn.flip List.take limit

  (* [x = y => u = v] for a frame equation [u = v] ([frame_equations] at the
     same [limit]) and an equation [x = y] between integer terms the unknown
     reaches ([int_terms]) rooted at different parameters, each pair once.
     The guard is the outer loop, so a small limit keeps every frame
     equation under the first guards rather than one equation under every
     guard.  Contract: [limit <= 0] gives [[]]; otherwise at most [limit]
     quantifier-free implications over [params], without repetition by
     printed form.  A function of [params]' names and sorts only. *)
  let guarded_frame_equations ?(stop = fun () -> false) ~limit
      (params : sort_env_list) =
    if limit <= 0 then []
    else
      let frames = frame_equations ~stop ~limit params in
      let ints =
        List.concat_mapi params ~f:(fun i (x, s) ->
            List.map (int_terms [ (x, s) ]) ~f:(fun t -> (i, t)))
      in
      let guards =
        List.concat_map ints ~f:(fun (i1, x) ->
            List.filter_map ints ~f:(fun (i2, y) ->
                if i1 < i2 then Some (Formula.eq x y) else None))
      in
      let seen = Hash_set.create (module String) in
      List.concat_map guards ~f:(fun g ->
          List.map frames ~f:(fun f ->
              poll stop;
              Formula.mk_imply g f))
      |> List.filter ~f:(fun phi ->
             let key = Formula.str_of phi in
             if Hash_set.mem seen key then false
             else (
               Hash_set.add seen key;
               true))
      |> Fn.flip List.take limit

  (* oriented inequalities over the integer terms an unknown reaches
     ([int_terms]), in this order: the sign facts [0 <= t] and [t = 0]; the
     orders [t1 <= t2]; and the differences [t1 <= t2 - t3] -- the bounds a loop
     keeps between a counter, its limits and a length ([st <= it.0],
     [len out <= it.0 - st], [n <= e.cur.1]).  Both [t1 <= t2 - t3] and
     [t3 <= t2 - t1] are produced although they are one linear fact: which of
     the two reads as the contract wrote it depends on the input, and the
     deduplication below is by normal form, which does not always identify
     them.  The first [limit] in that order
     after deduplication by normal form, so a small limit keeps the signs and
     the orders and the cubic family comes last. *)
  let inequalities ?(stop = fun () -> false) ~limit (params : sort_env_list) =
    if limit <= 0 then []
    else
      let ts = List.mapi (int_terms params) ~f:(fun i t -> (i, t)) in
      let zero = T_int.zero () in
      let signs =
        List.concat_map ts ~f:(fun (_, t) ->
            [ Formula.leq zero t; Formula.eq t zero ])
      in
      let orders =
        List.concat_map ts ~f:(fun (i1, t1) ->
            List.filter_map ts ~f:(fun (i2, t2) ->
                if i1 <> i2 then Some (Formula.leq t1 t2) else None))
      in
      let diffs =
        List.concat_map ts ~f:(fun (i1, t1) ->
            List.concat_map ts ~f:(fun (i2, t2) ->
                List.filter_map ts ~f:(fun (i3, t3) ->
                    poll stop;
                    if i1 <> i3 && i2 <> i1 && i2 <> i3 then
                      Some (Formula.leq t1 (T_int.mk_sub t2 t3))
                    else None)))
      in
      let seen = Hash_set.create (module String) in
      let rec take n acc = function
        | [] -> List.rev acc
        | _ when n <= 0 -> List.rev acc
        | phi :: rest ->
            poll stop;
            let phi = normal phi in
            let key = Formula.str_of phi in
            if literal phi || Hash_set.mem seen key then take n acc rest
            else (
              Hash_set.add seen key;
              take (n - 1) (phi :: acc) rest)
      in
      (* the lists are built whole: at most (terms)^3 small formulas, which a
         signature with a few dozen integer terms keeps in the thousands *)
      take limit [] (signs @ orders @ diffs)

  (* whether a quantified formula is a definition in disguise: an
     existential with a conjunct, or a universal with a disjunct, that is an
     equation (resp. a disequation) over a bound variable -- the shape a
     [let] or a one-point rule leaves ([exists v. v = t /\ ...]), which says
     nothing a candidate needs and whose instances only cost questions *)
  let one_point = function
    | Formula.Bind (binder, bs, body, _) ->
        let bound = Set.Poly.of_list (List.map bs ~f:fst) in
        let mentions q = not (Set.are_disjoint (Formula.tvs_of q) bound) in
        let is_neq = function
          | Formula.UnaryOp (Formula.Not, q, _) -> Formula.is_eq q
          | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ _; _ ], _), _)
            ->
              true
          | _ -> false
        in
        (match binder with
        | Formula.Exists ->
            Set.exists (Formula.conjuncts_of body) ~f:(fun q ->
                Formula.is_eq q && mentions q)
        | Formula.Forall ->
            Set.exists (Formula.disjuncts_of body) ~f:(fun q ->
                is_neq q && mentions q)
        | _ -> false)
    | _ -> false

  (* the maximal quantified subformulas of [phi] that apply no unknown and
     are not [one_point], looking through the ones that are *)
  let rec quantified_subformulas acc phi =
    match phi with
    | Formula.Bind (_, _, body, _)
      when Set.is_empty (Formula.pvs_of phi) && one_point phi ->
        (* a [let] in disguise: look inside it, where its bound variable is
           one more free variable to fill *)
        quantified_subformulas acc body
    | Formula.Bind (_, _, _, _) when Set.is_empty (Formula.pvs_of phi) ->
        phi :: acc
    | Formula.UnaryOp (_, phi, _) -> quantified_subformulas acc phi
    | Formula.BinaryOp (_, phi1, phi2, _) ->
        quantified_subformulas (quantified_subformulas acc phi1) phi2
    | Formula.Bind (_, _, phi, _) -> quantified_subformulas acc phi
    | Formula.LetFormula (_, _, _, phi, _) -> quantified_subformulas acc phi
    | _ -> acc

  (* the quantified facts the input states, moved onto the unknown: each
     maximal quantified subformula of a formula of [sources] that applies no
     unknown, with each of its free variables replaced by a term of the same
     sort the unknown reaches, at most [limit] instantiations per subformula.
     A contract's postcondition stated over a call's result
     ([forall j. 0 <= j < len r => r[j] >= k]) becomes the same fact over the
     loop's accumulator.  A subformula with a free variable of a sort no
     parameter reaches is skipped.  [sources] is a list of groups in priority
     order (the input's own assertions before the preprocessed clauses, whose
     quantifiers are mostly the ones preprocessing introduced); within a
     group the universals come before the existentials and the smaller before
     the larger, and the first [limit] atoms in that order after
     deduplication by normal form are kept. *)
  (* With [frame] (a sublist of [params]), the subformulas instantiated are
     the ones without it, and each of them that has a free variable of an
     opaque sort (a sort variable, an uninterpreted sort, a datatype) some
     term reached from [frame] has is instantiated afresh, every such variable
     filled from the frame terms only, in place of its instances of before; a subformula with no such variable keeps its instances.  So the
     subformulas are the same as without [frame] (a quota left over by a
     subformula that now has fewer instances is not refilled from other facts:
     that brought heavier universals in, which as hypotheses slowed every
     question of a pass), and the instances differ only in where they put
     their frame-sorted variables.  [frame] is meant to be the parameters
     every loop of the unknown passes on unchanged ([frame_positions]): a
     fact the input states about a function's own arguments (a precondition
     over [iter], [init], [f]) is inductive over a loop that keeps those
     arguments, while its instances at the loop's moving values (the current
     iterator, the accumulator, the closure state) are typically not, each
     cost the pre-pass a question that the solver could leave undecided at its
     whole budget, and the instance at the kept values may not have been among
     the first [limit] at all.  With [frame = []] the atoms are those of
     before.  Only which candidates are offered changes, so this can lose an
     answer (an instance at a moving value that was needed) and never make
     one wrong. *)
  let quantified_facts ?(stop = fun () -> false) ?(frame = []) ~limit
      ~(sources : Formula.t list list) (params : sort_env_list) =
    if limit <= 0 then []
    else
      let pset = Set.Poly.of_list (List.map params ~f:fst) in
      let instances_with reached q =
        let fvs = Set.to_list (Formula.term_sort_env_of q) in
        let cands = List.map fvs ~f:(fun (_, s) -> reached s) in
        if List.exists cands ~f:List.is_empty then []
        else
          List.filter_map (tuples limit cands) ~f:(fun ts ->
              poll stop;
              let sub =
                Map.Poly.of_alist_exn (List.zip_exn (List.map fvs ~f:fst) ts)
              in
              let q = Formula.subst sub q in
              if Set.is_subset (Formula.tvs_of q) ~of_:pset then Some q
              else None)
      in
      let instances = instances_with (reached_of_sort params) in
      (* the sorts the restriction applies to: a sort variable, an
         uninterpreted sort or a datatype -- the values a program passes
         around without comparing them by size (a closure's state, an
         iterator, an accumulator of a generic type).  An integer, real,
         Boolean, bit-vector, sequence or array variable is filled as before:
         a fact over those is typically a range or a length relation between
         a kept bound and a moving counter ([forall x. lo <= x < cur => ...]),
         and the moving instance is the one a loop needs *)
      let opaque = function
        | Sort.SVar _ | T_dt.SUS _ | T_dt.SDT _ -> true
        | _ -> false
      in
      let frame_terms s =
        if opaque s then reached_of_sort frame s else []
      in
      (* whether [q] has a free variable of such a sort a frame term has *)
      let frame_sorted q =
        (not (List.is_empty frame))
        && Set.exists (Formula.term_sort_env_of q) ~f:(fun (_, s) ->
               not (List.is_empty (frame_terms s)))
      in
      let frame_instances =
        instances_with (fun s ->
            match frame_terms s with
            | [] -> reached_of_sort params s
            | ts -> ts)
      in
      let normal_atoms phis =
        List.filter_map phis ~f:(fun phi ->
            poll stop;
            let phi = normal phi in
            if literal phi then None else Some (Formula.str_of phi, phi))
      in
      (* each atom with the subformula it instantiates *)
      let rank group =
        List.fold group ~init:[] ~f:quantified_subformulas
        |> List.concat_map ~f:(fun q ->
               List.map (normal_atoms (instances q)) ~f:(fun (k, p) -> (k, p, q)))
        |> List.dedup_and_sort ~compare:(fun (s1, p1, _) (s2, p2, _) ->
               match
                 Bool.compare (Formula.is_exists p1) (Formula.is_exists p2)
               with
               | 0 -> (
                   match
                     Int.compare (Formula.ast_size p1) (Formula.ast_size p2)
                   with
                   | 0 -> String.compare s1 s2
                   | c -> c)
               | c -> c)
      in
      let seen = Hash_set.create (module String) in
      let selected =
        List.concat_map sources ~f:rank
        |> List.filter ~f:(fun (key, _, _) ->
               if Hash_set.mem seen key then false
               else (
                 Hash_set.add seen key;
                 true))
        |> Fn.flip List.take limit
      in
      if List.is_empty frame then List.map selected ~f:(fun (_, p, _) -> p)
      else
        (* each frame-sorted subformula's atoms replaced, at the place of its
           first one, by its frame instances *)
        let out = Hash_set.create (module String) in
        let replaced = Hash_set.create (module String) in
        List.concat_map selected ~f:(fun (key, phi, q) ->
            if not (frame_sorted q) then
              if Hash_set.mem out key then []
              else (
                Hash_set.add out key;
                [ phi ])
            else
              let qk = Formula.str_of q in
              if Hash_set.mem replaced qk then []
              else (
                Hash_set.add replaced qk;
                List.filter_map (normal_atoms (frame_instances q))
                  ~f:(fun (k, p) ->
                    if Hash_set.mem out k then None
                    else (
                      Hash_set.add out k;
                      Some p))))

  (* The parameter positions (from 0) of the unknown [p] that every clause
     applying [p] both in its head and in its body passes on unchanged: at
     such a position, each head application and each body application of [p]
     in the clause have the same variable.  [[]] when no clause applies [p]
     on both sides (no loop, so nothing is kept by one), and a position where
     some clause passes anything other than one same variable (a term, or two
     variables an equation of the clause's pure part identifies) is not
     reported: the test is syntactic and can only answer [false] where the
     position is in fact unchanged.  A function of the clauses only. *)
  let frame_positions (clauses : Clause.t list) (p : Ident.tvar) : int list =
    let apps atoms =
      List.filter_map (Set.to_list atoms) ~f:(fun a ->
          match Logic.Term.let_apps a with
          | Logic.Var (q, _), args when Ident.tvar_equal p q -> Some args
          | _ -> None)
    in
    let loops =
      List.filter_map clauses ~f:(fun ((_, ps, ns, _) : Clause.t) ->
          match (apps ps, apps ns) with
          | [], _ | _, [] -> None
          | hs, bs -> Some (hs @ bs))
    in
    match loops with
    | [] -> []
    | (first :: _) :: _ ->
        List.filter (List.range 0 (List.length first)) ~f:(fun i ->
            List.for_all loops ~f:(fun apps ->
                match
                  List.map apps ~f:(fun args ->
                      match List.nth args i with
                      | Some (Logic.Var (x, _)) -> Some x
                      | _ -> None)
                with
                | Some x :: rest ->
                    List.for_all rest ~f:(function
                      | Some y -> Ident.tvar_equal x y
                      | None -> false)
                | _ -> false))
    | [] :: _ -> []

  (* Relation inclusions between two reached terms: for a relation [R] the
     unknown carries -- a reached term whose sort is an array, curried to
     depth k >= 2, ending in [Bool], as in [memberships] -- with first index
     sort [s], and for each ordered pair [(t1, t2)] of distinct terms (by
     printed form) of sort [s] reached from all of [params],
       [forall x2 ... xk. R[t1][x2]...[xk] = true => R[t2][x2]...[xk] = true];
     and for a non-recursive Bool-valued definition [d] of [defs] with k >= 2
     formals, the first of sort [s], the same with [d]'s body instantiated
     ([forall x2 ... xk. d(t1, x2, ...) => d(t2, x2, ...)]).  This is the
     fact a loop keeps between an iterator's entry state and its current one
     ([forall x. produces(cur it, x) => produces(cur e, x)]): what remains to
     be produced from here was producible from the start.

     Contract: [limit <= 0] gives [[]]; otherwise at most [limit] pairs per
     relation or definition and at most [limit] atoms in all (the smallest
     by [Formula.ast_size] after normalisation, [smallest]); every atom is a
     universal whose free variables are among [params] (the bound names are
     chosen apart from [params], so no parameter is captured); a relation of
     depth 1 or a definition of one formal gives nothing (there is no
     remaining argument to quantify, and the quantifier-free implication is
     not a conjunct a loop invariant usually needs); a sort with fewer than two
     reached terms gives nothing.  A function of [params]' names and sorts and
     of [defs] only.  [stop] is polled once per atom built, as in the other
     families, so the pre-pass's whole-pass budget covers this one too. *)
  (* The syntactic test behind [houdini_inclusions_skip_constructor_equations].
     [constructor_equation_body ~varied ~rest body] holds when [body] is an
     equation, either side first, between a variable [x] of [rest] and a
     constructor application [c(u1, ..., un)] such that [x] occurs in no
     [ui], [varied] occurs in some [ui], and every [ui] that mentions
     [varied] IS the variable [varied].

     Equivalence (in the standard structure, where a datatype is its term
     algebra and a constructor is injective): with [d] that definition,
     [forall rest'. d(t1, rest') => d(t2, rest')] is
     [forall rest'. x = c(u[t1]) => x = c(u[t2])]; instantiating [x] at
     [c(u[t1])] (the one-point rule, sound because [x] is not in the [ui])
     gives [forall rest''. c(u[t1]) = c(u[t2])], by injectivity
     [forall rest''. /\ ui[t1] = ui[t2]]; an argument without [varied] gives
     [ui = ui], and one that is [varied] gives [t1 = t2], so the inclusion
     is equivalent to [t1 = t2], and [t1 = t2] implies it back.  The frame
     family offers that equation exactly when [t1] and [t2] start at two
     different parameters and their sort is [equatable] ([skip_pair]); for
     a pair of one parameter, or of a Boolean or array sort, the inclusion
     is kept.  An argument that is a proper function of [varied] ([fst a],
     [a + 1]) makes the inclusion only implied by [t1 = t2], strictly
     weaker, so it is not skipped: an invariant may need the weaker fact.
     The frame family's own [limit] may still cut the equation; the skip
     does not look at that cut. *)
  let constructor_equation_body ~varied ~(rest : sort_env_list) body =
    Formula.is_eq body
    &&
    let l, r, _ = Formula.let_eq body in
    let rest_vars = Set.Poly.of_list (List.map rest ~f:fst) in
    let mentions v u = Set.mem (Term.tvs_of u) v in
    let shape x c =
      match (x, c) with
      | Term.Var (x, _, _), Term.FunApp (T_dt.DTCons _, us, _)
        when Set.mem rest_vars x ->
          (not (List.exists us ~f:(mentions x)))
          && List.exists us ~f:(mentions varied)
          && List.for_all us ~f:(fun u ->
                 (not (mentions varied u))
                 ||
                 match u with
                 | Term.Var (y, _, _) -> Stdlib.(y = varied)
                 | _ -> false)
      | _ -> false
    in
    shape l r || shape r l

  (* the pairs of reached terms the frame family equates: two different
     starting parameters (each reached term mentions exactly its parameter)
     and an [equatable] sort *)
  let skip_pair t1 t2 =
    equatable (Term.sort_of t1)
    && not (Set.equal (Term.tvs_of t1) (Term.tvs_of t2))

  let inclusions ?(stop = fun () -> false)
      ?(skip_constructor_equations = false) ~limit ~(defs : FunEnv.t)
      (params : sort_env_list) =
    if limit <= 0 then []
    else
      let pset = Set.Poly.of_list (List.map params ~f:fst) in
      let over_params q = Set.is_subset (Formula.tvs_of q) ~of_:pset in
      (* bound names [hincl1, hincl2, ...], each made apart from [params] *)
      let binders sorts =
        List.mapi sorts ~f:(fun i s ->
            let rec pick name =
              if Set.mem pset (Ident.Tvar name) then pick (name ^ "_")
              else Ident.Tvar name
            in
            (pick (sprintf "hincl%d" (i + 1)), s))
      in
      let distinct_reached s =
        List.dedup_and_sort (reached_of_sort params s) ~compare:(fun a b ->
            String.compare (Term.str_of a) (Term.str_of b))
      in
      let pairs ts =
        List.take
          (List.concat_map ts ~f:(fun t1 ->
               List.filter_map ts ~f:(fun t2 ->
                   if String.equal (Term.str_of t1) (Term.str_of t2) then None
                   else Some (t1, t2))))
          limit
      in
      let rels =
        List.concat_map (reached params) ~f:(fun (_, r) ->
            match CellQual.uncurry_array_sort (Term.sort_of r) with
            | s :: (_ :: _ as rest), e when Term.is_bool_sort e ->
                let bs = binders rest in
                let xs = List.map bs ~f:(fun (x, s) -> Term.mk_var x s) in
                let mem t =
                  Formula.eq
                    (T_array.mk_select_app r (t :: xs))
                    (T_bool.mk_true ())
                in
                List.map (pairs (distinct_reached s)) ~f:(fun (t1, t2) ->
                    poll stop;
                    Formula.forall bs (Formula.mk_imply (mem t1) (mem t2)))
            | _ -> [])
      in
      let defined =
        Map.Poly.to_alist defs
        |> List.concat_map ~f:(fun (_, (fargs, sret, body, isrec, _)) ->
               match fargs with
               | (f1, s) :: (_ :: _ as rest)
                 when (not isrec) && Term.is_bool_sort sret ->
                   let bs = binders (List.map rest ~f:snd) in
                   let body = Formula.of_bool_term body in
                   let ctor_eq =
                     skip_constructor_equations
                     && constructor_equation_body ~varied:f1 ~rest body
                   in
                   let inst t =
                     Formula.subst
                       (Map.Poly.of_alist_exn
                          ((f1, t)
                          :: List.map2_exn rest bs ~f:(fun (y, _) (x, s) ->
                                 (y, Term.mk_var x s))))
                       body
                   in
                   List.filter_map (pairs (distinct_reached s))
                     ~f:(fun (t1, t2) ->
                       poll stop;
                       if ctor_eq && skip_pair t1 t2 then None
                       else
                         let q =
                           Formula.forall bs
                             (Formula.mk_imply (inst t1) (inst t2))
                         in
                         if over_params q then Some q else None)
               | _ -> [])
      in
      smallest ~stop ~limit (rels @ defined)

  (* {3 Counting families: length sums, affine elements, three-term
     equations}

     Three families over the integer and sequence terms an unknown reaches
     ([reached]), for the facts a loop over a counting range keeps: how many
     items it has collected, what they are, and how far it has gone. *)

  (* [atoms] with each atom normalised, without literals and repetitions (by
     the printed normal form), at most [limit], taken in the order of the
     atoms' sizes BEFORE normalisation (ties by printed form): unlike
     [smallest], only the atoms up to the [limit]-th distinct one are
     normalised, so a cubic family costs [limit] normalisations and a sort *)
  let smallest_raw ?(stop = fun () -> false) ~limit atoms =
    let sorted =
      List.map atoms ~f:(fun phi -> (Formula.ast_size phi, Formula.str_of phi, phi))
      |> List.sort ~compare:(fun (n1, s1, _) (n2, s2, _) ->
             match Int.compare n1 n2 with 0 -> String.compare s1 s2 | c -> c)
    in
    let seen = Hash_set.create (module String) in
    let rec take n acc = function
      | [] -> List.rev acc
      | _ when n <= 0 -> List.rev acc
      | (_, _, phi) :: rest ->
          poll stop;
          let phi = normal phi in
          let key = Formula.str_of phi in
          if literal phi || Hash_set.mem seen key then take n acc rest
          else (
            Hash_set.add seen key;
            take (n - 1) (phi :: acc) rest)
    in
    take limit [] sorted

  (* the reached integer terms and the reached sequence terms, each without
     repetition by printed form, in [reached]'s order *)
  let ints_and_seqs (params : sort_env_list) =
    let dedup ts =
      let seen = Hash_set.create (module String) in
      List.filter ts ~f:(fun t ->
          let k = Term.str_of t in
          if Hash_set.mem seen k then false
          else (
            Hash_set.add seen k;
            true))
    in
    let ts = List.map (reached params) ~f:snd in
    ( dedup (List.filter ts ~f:(fun t -> Term.is_int_sort (Term.sort_of t))),
      dedup
        (List.filter ts ~f:(fun t ->
             match Term.sort_of t with T_seq.SSeq _ -> true | _ -> false)) )

  let same_term t1 t2 = String.equal (Term.str_of t1) (Term.str_of t2)

  (* Empty-guarded frame equations: [len s = 0 => u = v] for [s] a reached
     sequence and [u = v] a frame equation ([frame_equations] at the same
     [limit]) -- [len sk = 0 => m.0 = s.0]: while the history a loop keeps
     is empty, the iterator it advances is still the one it started from,
     and the unguarded frame equation is refuted by the step clause.  The
     guards of [guarded_frame_equations] equate two reached integer terms and
     cannot say this, since [0] is not a reached term.  The sequence is the
     outer loop, so a small limit keeps every frame equation under the first
     sequences rather than one equation under every sequence.

     Contract: [limit <= 0] gives [[]]; otherwise at most [limit]
     quantifier-free implications whose free variables are among [params],
     without repetition by printed form, each [len s = 0 => e] with [s] a
     reached sequence term and [e] one of [frame_equations ~limit params];
     no reached sequence, or no frame equation, gives nothing.  A function of
     [params]' names and sorts only; [stop] is polled once per atom built. *)
  let empty_guarded_frames ?(stop = fun () -> false) ~limit
      (params : sort_env_list) =
    if limit <= 0 then []
    else
      let _, seqs = ints_and_seqs params in
      let frames =
        if List.is_empty seqs then [] else frame_equations ~stop ~limit params
      in
      let seen = Hash_set.create (module String) in
      List.concat_map seqs ~f:(fun s ->
          match Term.sort_of s with
          | T_seq.SSeq se ->
              let guard = Formula.eq (T_seq.mk_len se s) (T_int.zero ()) in
              List.map frames ~f:(fun f ->
                  poll stop;
                  Formula.mk_imply guard f)
          | _ -> [])
      |> List.filter ~f:(fun phi ->
             let key = Formula.str_of phi in
             if Hash_set.mem seen key then false
             else (
               Hash_set.add seen key;
               true))
      |> Fn.flip List.take limit

  (* Length sums: [len s + x = t] (written [len s = t] when [x] is zero) for
     [s] a reached sequence, [x] zero or a reached integer term, and [t] a
     reached integer term or the length of another reached sequence, with
     [t] neither [x] nor [len s] -- [len out + a.0 = b.0], the number of
     items a loop has collected from a range it has advanced from [a] to
     [b].

     Contract: [limit <= 0] gives [[]]; otherwise at most [limit] atoms, each
     a normalised equation whose free variables are among [params], the
     smallest before normalisation first ([smallest_raw]), so the [x = 0]
     forms come before the shifted ones; no sequence reached gives nothing.
     A function of [params]' names and sorts only; [stop] is polled once
     per atom built and once per atom normalised. *)
  let length_sums ?(stop = fun () -> false) ~limit (params : sort_env_list) =
    if limit <= 0 then []
    else
      let ints, seqs = ints_and_seqs params in
      let len_of s =
        match Term.sort_of s with
        | T_seq.SSeq se -> T_seq.mk_len se s
        | _ -> assert false
      in
      let lens = List.map seqs ~f:len_of in
      let shifts = T_int.zero () :: ints in
      smallest_raw ~stop ~limit
      @@ List.concat_map lens ~f:(fun len ->
             List.concat_map shifts ~f:(fun x ->
                 List.filter_map (ints @ lens) ~f:(fun t ->
                     poll stop;
                     if same_term t x || same_term t len then None
                     else
                       let lhs =
                         if T_int.is_zero x then len else T_int.mk_add len x
                       in
                       Some (Formula.eq lhs t))))

  (* Last-element equations: [v = s[len t]] for [v] a reached term, [s] a
     reached sequence whose elements have [v]'s sort and [t] another reached
     sequence -- [g = fs[len s]]: a loop that keeps its history in ghost
     sequences holds the current value (the closure's state, the
     accumulator) as the last entry of a history one longer than the history
     of produced items, and no other family states it, since [len t] reaches
     no parameter.

     Contract: [limit <= 0] gives [[]]; otherwise at most [limit] atoms, each
     a normalised equation whose free variables are among [params], the
     smallest before normalisation first ([smallest_raw]); no reached
     sequence of a reached term's sort gives nothing, and [s[len s]] (a read
     past the end) is never built.  A function of [params]' names and sorts
     only; [stop] is polled once per atom built and once per atom
     normalised. *)
  let last_element_equations ?(stop = fun () -> false) ~limit
      (params : sort_env_list) =
    if limit <= 0 then []
    else
      let _, seqs = ints_and_seqs params in
      let vs =
        List.filter_map (reached params) ~f:(fun (_, v) ->
            let s = Term.sort_of v in
            if equatable s then Some v else None)
      in
      smallest_raw ~stop ~limit
      @@ List.concat_map seqs ~f:(fun s ->
             match Term.sort_of s with
             | T_seq.SSeq se ->
                 List.concat_map seqs ~f:(fun t ->
                     if same_term s t then []
                     else
                       let len_t =
                         match Term.sort_of t with
                         | T_seq.SSeq te -> T_seq.mk_len te t
                         | _ -> assert false
                       in
                       List.filter_map vs ~f:(fun v ->
                           poll stop;
                           if
                             String.equal
                               (Term.str_of_sort (Term.sort_of v))
                               (Term.str_of_sort se)
                           then Some (Formula.eq v (T_seq.mk_nth se s len_t))
                           else None))
             | _ -> [])

  (* Affine elements: [forall i. 0 <= i /\ i < len s => s[i] = t + i]
     (written [s[i] = i] when [t] is zero) for [s] a reached sequence of
     integers and [t] zero or a reached integer term (another reached
     sequence's length included, never [len s] itself) -- [out[i] = a.0 + i],
     the content of a sequence collected from the range starting at [a.0].

     Contract: [limit <= 0] gives [[]]; otherwise at most [limit] atoms, the
     smallest after normalisation first ([smallest]); every atom is a
     universal over one integer whose free variables are among [params], the
     bound name chosen apart from [params] so no parameter is captured; no
     reached sequence of integers gives nothing.  A function of [params]'
     names and sorts only; [stop] is polled once per atom built. *)
  let affine_elements ?(stop = fun () -> false) ~limit (params : sort_env_list)
      =
    if limit <= 0 then []
    else
      let pset = Set.Poly.of_list (List.map params ~f:fst) in
      let rec pick name =
        if Set.mem pset (Ident.Tvar name) then pick (name ^ "_")
        else Ident.Tvar name
      in
      let i = (pick "haff", T_int.SInt) in
      let iv = Term.mk_var (fst i) T_int.SInt in
      let ints, seqs = ints_and_seqs params in
      let int_seqs =
        List.filter seqs ~f:(fun s ->
            match Term.sort_of s with
            | T_seq.SSeq se -> Term.is_int_sort se
            | _ -> false)
      in
      let lens =
        List.map seqs ~f:(fun s ->
            match Term.sort_of s with
            | T_seq.SSeq se -> (s, T_seq.mk_len se s)
            | _ -> assert false)
      in
      smallest ~stop ~limit
      @@ List.concat_map int_seqs ~f:(fun s ->
             let len = T_seq.mk_len T_int.SInt s in
             let offsets =
               (T_int.zero () :: ints)
               @ List.filter_map lens ~f:(fun (u, l) ->
                     if same_term u s then None else Some l)
             in
             List.map offsets ~f:(fun t ->
                 poll stop;
                 let value = if T_int.is_zero t then iv else T_int.mk_add t iv in
                 Formula.forall [ i ]
                   (Formula.mk_imply
                      (Formula.and_of
                         [ Formula.leq (T_int.zero ()) iv; Formula.lt iv len ])
                      (Formula.eq (T_seq.mk_nth T_int.SInt s iv) value))))

  (* Prefix elements: [forall i. 0 <= i /\ i < x => s[i] = c] for [s] a
     reached sequence of integers, [x] a reached integer term (the length of
     another reached sequence included, never [len s] itself) and [c] one of
     [consts] -- the part of a sequence a loop has already overwritten with a
     constant ([fin[i] = 0] below the iterator's position), which no fact
     over the whole sequence states and which a contract's postcondition
     states only for the full range.

     Contract: [limit <= 0] or [consts = []] gives [[]]; otherwise at most
     [limit] atoms, in the order of [consts], then of the sequences, then of
     the bounds (not re-ranked by size: all atoms of the family have one
     shape), without repetition by printed normal form; every atom is a
     universal over one integer whose free variables are among [params], the
     bound name chosen apart from [params] so no parameter is captured; no
     reached sequence of integers or no reached integer term gives nothing.
     A function of [params]' names and sorts and of [consts] only; [stop] is
     polled once per atom built. *)
  let prefix_elements ?(stop = fun () -> false) ~limit ~(consts : Term.t list)
      (params : sort_env_list) =
    if limit <= 0 || List.is_empty consts then []
    else
      let pset = Set.Poly.of_list (List.map params ~f:fst) in
      let rec pick name =
        if Set.mem pset (Ident.Tvar name) then pick (name ^ "_")
        else Ident.Tvar name
      in
      let i = (pick "hpre", T_int.SInt) in
      let iv = Term.mk_var (fst i) T_int.SInt in
      let ints, seqs = ints_and_seqs params in
      let int_seqs =
        List.filter seqs ~f:(fun s ->
            match Term.sort_of s with
            | T_seq.SSeq se -> Term.is_int_sort se
            | _ -> false)
      in
      let lens =
        List.map seqs ~f:(fun s ->
            match Term.sort_of s with
            | T_seq.SSeq se -> (s, T_seq.mk_len se s)
            | _ -> assert false)
      in
      let seen = Hash_set.create (module String) in
      List.concat_map consts ~f:(fun c ->
          List.concat_map int_seqs ~f:(fun s ->
              let bounds =
                ints
                @ List.filter_map lens ~f:(fun (u, l) ->
                      if same_term u s then None else Some l)
              in
              List.map bounds ~f:(fun x -> (c, x, s))))
      |> List.filter_map ~f:(fun (c, x, s) ->
             poll stop;
             let phi =
               normal
               @@ Formula.forall [ i ]
                    (Formula.mk_imply
                       (Formula.and_of
                          [ Formula.leq (T_int.zero ()) iv; Formula.lt iv x ])
                       (Formula.eq (T_seq.mk_nth T_int.SInt s iv) c))
             in
             let key = Formula.str_of phi in
             if literal phi || Hash_set.mem seen key then None
             else (
               Hash_set.add seen key;
               Some phi))
      |> Fn.flip List.take limit

  (* the integer literals of [phis], each once, the smallest in absolute
     value first, at most [n]: the constants a loop writes are among the
     program's own literals *)
  let sorted_int_literals (phis : Formula.t list) =
    List.concat_map phis ~f:(fun phi ->
        Set.to_list (Formula.filtered_terms_of ~f:T_int.is_int phi))
    |> List.dedup_and_sort ~compare:(fun t1 t2 ->
           let n1 = T_int.let_int t1 and n2 = T_int.let_int t2 in
           match Z.compare (Z.abs n1) (Z.abs n2) with
           | 0 -> Z.compare n1 n2
           | c -> c)

  let int_literals ~n phis = List.take (sorted_int_literals phis) n

  (* The input's assertions are read here in two ways only: as a group of
     [quantified_facts]' sources and through [int_literals].  A group [g] and
     the reversed list of its maximal quantified subformulas,
     [List.rev (List.fold g ~init:[] ~f:quantified_subformulas)], give
     [quantified_facts] the same list: each element of the second is a
     quantified formula that applies no unknown and is not [one_point], which
     [quantified_subformulas] returns whole, so folding over the reversed list
     rebuilds the list.  And [int_literals ~n] is a prefix of
     [sorted_int_literals].  So the digest below answers both readers exactly
     as the assertions do, and it is all of them that has to be held. *)
  let quantified_group phis =
    List.rev (List.fold phis ~init:[] ~f:quantified_subformulas)

  let digest_input_assertions () =
    match LogicOld.get_input_record () with
    | LogicOld.InputAsRead phis ->
        LogicOld.set_input_record
          (LogicOld.InputDigest
             {
               quantified = quantified_group phis;
               int_literals = sorted_int_literals phis;
             })
    | LogicOld.InputDigest _ -> ()

  let input_quantified_group () =
    match LogicOld.get_input_record () with
    | LogicOld.InputAsRead phis -> phis
    | LogicOld.InputDigest { quantified; _ } -> quantified

  let input_int_literals ~n =
    match LogicOld.get_input_record () with
    | LogicOld.InputAsRead phis -> int_literals ~n phis
    | LogicOld.InputDigest { int_literals; _ } -> List.take int_literals n

  (* Three-term equations: [x = y - z] for three distinct reached integer
     terms (sequence lengths included, as in [int_terms]) -- [n = b.0 - it0.0],
     a counter equal to the distance between two positions.  [x = y - z] and
     [z = y - x] are one linear fact: only the one with [x] before [z] in
     [int_terms]' order is built, which halves the atoms built, and the two
     would anyway share a normal form ([0 = y - x - z]), which the
     deduplication of [smallest_raw] identifies.

     Contract: [limit <= 0] gives [[]]; otherwise at most [limit] atoms, each
     a normalised equation over [params], the smallest before normalisation
     first ([smallest_raw]); fewer than three distinct terms give nothing.  A
     function of [params]' names and sorts only; [stop] is polled once per
     atom built and once per atom normalised. *)
  let three_term_equations ?(stop = fun () -> false) ~limit
      (params : sort_env_list) =
    if limit <= 0 then []
    else
      let ts =
        let seen = Hash_set.create (module String) in
        List.filter (int_terms params) ~f:(fun t ->
            let k = Term.str_of t in
            if Hash_set.mem seen k then false
            else (
              Hash_set.add seen k;
              true))
        |> List.mapi ~f:(fun i t -> (i, t))
      in
      smallest_raw ~stop ~limit
      @@ List.concat_map ts ~f:(fun (ix, x) ->
             List.concat_map ts ~f:(fun (iy, y) ->
                 List.filter_map ts ~f:(fun (iz, z) ->
                     poll stop;
                     if ix < iz && iy <> ix && iy <> iz then
                       Some (Formula.eq x (T_int.mk_sub y z))
                     else None)))

  (* Guarded orders: [len s = 0 \/ t1 <= t2] for [s] a reached sequence and
     [t1], [t2] two distinct reached integer terms (sequence lengths not
     included) -- [len out = 0 \/ b.0 <= b.1]: a range iterator that has
     produced an item was not past its end, while the empty production
     starts from any range, so the unguarded order is refuted by the fact
     clause and only the guarded one is inductive.

     Contract: [limit <= 0] gives [[]]; otherwise at most [limit] atoms, each
     a normalised disjunction over [params], the smallest before
     normalisation first ([smallest_raw]); no reached sequence, or fewer than
     two reached integer terms, gives nothing.  A function of [params]'
     names and sorts only; [stop] is polled once per atom built and once per
     atom normalised. *)
  let guarded_orders ?(stop = fun () -> false) ~limit (params : sort_env_list)
      =
    if limit <= 0 then []
    else
      let ints, seqs = ints_and_seqs params in
      smallest_raw ~stop ~limit
      @@ List.concat_map seqs ~f:(fun s ->
             let empty =
               match Term.sort_of s with
               | T_seq.SSeq se -> Formula.eq (T_seq.mk_len se s) (T_int.zero ())
               | _ -> assert false
             in
             List.concat_map ints ~f:(fun t1 ->
                 List.filter_map ints ~f:(fun t2 ->
                     poll stop;
                     if same_term t1 t2 then None
                     else Some (Formula.or_of [ empty; Formula.leq t1 t2 ]))))

  (* the keys a declared atom and a generated one are compared by in the
     census, so that two atoms that differ only in the names of their bound
     variables, the order of a quantified body's disjuncts (conjuncts under
     an existential) or the sides of an equation share a key: the printed
     normal form with the bound variables renamed in order of occurrence;
     for a quantified atom, its binder kind with the sorted printed parts of
     its body; for an equation, the one with its sides swapped *)
  let census_keys phi =
    let canon phi =
      let c = ref 0 in
      Formula.aconv_tvar_norm
        (fun () ->
          incr c;
          Ident.Tvar (sprintf "#hb%d" !c))
        (normal phi)
    in
    let phi = canon phi in
    let parts =
      match phi with
      | Formula.Bind (binder, bs, body, _) ->
          let ps =
            match binder with
            | Formula.Exists -> Formula.conjuncts_of body
            | _ -> Formula.disjuncts_of body
          in
          [
            sprintf "%s %s. %s"
              (Formula.str_of_binder binder)
              (String.concat_map_list ~sep:"," bs ~f:(snd >> Term.str_of_sort))
              (String.concat ~sep:" | "
              @@ List.sort ~compare:String.compare
              @@ List.map (Set.to_list ps) ~f:Formula.str_of);
          ]
      | _ -> []
    in
    let swapped =
      if Formula.is_eq phi then
        let t1, t2, _ = Formula.let_eq phi in
        [ Formula.str_of (canon (Formula.eq t2 t1)) ]
      else []
    in
    (Formula.str_of phi :: parts) @ swapped

  (* [premise_redundant clauses p params atom]: whether, in every clause
     that applies the unknown [p] (in its head or its body), each
     application's instance of [atom] (over [params], [p]'s parameters, put
     to the application's arguments) is a premise of the clause -- a
     conjunct of the negation of one of the disjuncts of the clause's pure
     part, compared by [census_keys] after [bool_eq_canon].  [false] when no clause applies [p]
     or an instance cannot be built.
     Why such an atom can be left out of a conjunctive candidate [C /\ a]
     for [p] without changing anything a clause says: at each application
     of [p] in a clause, [a]'s instance is already a premise of that clause,
     so a body application gains nothing from it and a head application's
     demand for it holds outright; [C] and [C /\ a] make each clause valid
     together or not at all.  The typical case is a law of a universally
     quantified function the unknown carries as a parameter (reflexivity of
     a history invariant) that the reader made a premise of every clause
     applying the unknown: generated as a candidate, it was asked once per
     clause and pass, and carried as a hypothesis by every other question.
     The test is syntactic and can only answer [false] where the atom is in
     fact redundant. *)
  (* [phi] with each equation or disequation between a Boolean term and a
     Boolean constant written one way: [(<false>) != t] where it says that
     [t] holds ([t = true], [true = t], [t != false]) and [(<false>) = t]
     where it says that it does not.  The reader writes a law's
     [R(x, x)] as [(<false>) != R[x][x]], a generated atom says
     [(<true>) = R[x][x]], and the two are one formula.  Equivalent to [phi]
     in every model. *)
  let bool_eq_canon phi =
    Formula.map_atom phi ~f:(fun atom ->
        match atom with
        | Atom.App (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as op), [ t1; t2 ], _)
          -> (
            let const t =
              if T_bool.is_true t then Some true
              else if T_bool.is_false t then Some false
              else None
            in
            let is_eq = match op with T_bool.Eq -> true | _ -> false in
            match (const t1, const t2) with
            | Some c, None | None, Some c ->
                let t = if Option.is_some (const t1) then t2 else t1 in
                let f = T_bool.mk_false () in
                Formula.mk_atom
                  (if Bool.equal is_eq c then T_bool.mk_neq f t
                   else T_bool.mk_eq f t)
            | _ -> Formula.mk_atom atom)
        | _ -> Formula.mk_atom atom)

  let premise_redundant (clauses : Clause.t list) (p : Ident.tvar)
      (params : sort_env_list) : Formula.t -> bool =
    let occurrences =
      List.filter_map clauses ~f:(fun ((uni_senv, ps, ns, phi) : Clause.t) ->
          let apps =
            List.filter_map (Set.to_list ps @ Set.to_list ns) ~f:(fun a ->
                match Logic.Term.let_apps a with
                | Logic.Var (q, _), args when Ident.tvar_equal p q -> Some args
                | _ -> None)
          in
          if List.is_empty apps then None
          else
            let premises =
              lazy
                (let keys = Hash_set.create (module String) in
                 (try
                    Logic.ExtTerm.to_old_fml Map.Poly.empty uni_senv phi
                    |> Formula.disjuncts_of |> Set.to_list
                    |> List.iter ~f:(fun d ->
                           Evaluator.simplify_neg d |> Formula.conjuncts_of
                           |> Set.iter ~f:(fun c ->
                                  List.iter
                                    (census_keys (bool_eq_canon c))
                                    ~f:(Hash_set.add keys)))
                  with exn_ when not (Common.Timer.is_async exn_) -> ());
                 keys)
            in
            Some (uni_senv, apps, premises))
    in
    fun atom ->
      (not (List.is_empty occurrences))
      && List.for_all occurrences ~f:(fun (uni_senv, apps, premises) ->
             List.for_all apps ~f:(fun args ->
                 match List.zip params args with
                 | List.Or_unequal_lengths.Unequal_lengths -> false
                 | Ok pairs -> (
                     try
                       let sub =
                         Map.Poly.of_alist_exn
                         @@ List.map pairs ~f:(fun ((x, _), t) ->
                                ( x,
                                  Logic.ExtTerm.to_old_trm Map.Poly.empty
                                    uni_senv t ))
                       in
                       let keys = Lazy.force premises in
                       List.exists
                         (census_keys (bool_eq_canon (Formula.subst sub atom)))
                         ~f:(Hash_set.mem keys)
                     with exn_ when not (Common.Timer.is_async exn_) ->
                       false)))
end

(* [houdini_drop_by_model] of the Houdini pre-pass: classic Houdini's
   conjunction question in front of the per-atom questions.  Kept outside
   [Make] so that it can be tested on its own. *)
module HoudiniByModel = struct
  (* What [model] makes of the ground instance [phi] of a candidate atom:
     [`False] or [`True] when substituting the model's values and simplifying
     decides it, [`Undecided] otherwise (a variable the model leaves out, an
     application of a function the simplifier does not evaluate, a quantifier
     it does not eliminate).  Sound in the one direction the caller relies
     on: [`False] only when [phi] is false in the model, since substitution
     and simplification preserve the value in it.  A model of an
     uninterpreted sort names its elements [<sort>!val!<n>], distinct names
     being distinct elements; the simplifier treats them as variables, so an
     equation between two of them is decided here by name. *)
  let instantiate (model : model) phi =
    let sub =
      Map.Poly.of_alist_reduce
        (List.filter_map model ~f:(function
          | (x, _), Some t -> Some (x, t)
          | _, None -> None))
        ~f:(fun t _ -> t)
    in
    let universe_element = function
      | Term.Var (Ident.Tvar n, _, _)
        when String.is_substring n ~substring:"!val!" ->
          Some n
      | _ -> None
    in
    let decide_elements phi =
      Evaluator.simplify
      @@ Formula.map_atom phi ~f:(fun atm ->
             match atm with
             | Atom.App
                 (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as op), [ t1; t2 ], _)
               -> (
                 match (universe_element t1, universe_element t2) with
                 | Some n1, Some n2 ->
                     Formula.mk_bool
                       (Bool.equal (String.equal n1 n2)
                          (match op with T_bool.Eq -> true | _ -> false))
                 | _ -> Formula.mk_atom atm)
             | _ -> Formula.mk_atom atm)
    in
    decide_elements @@ Evaluator.simplify @@ Formula.subst sub phi

  let judge (model : model) phi =
    try
      let phi = instantiate model phi in
      if Formula.is_false phi then `False
      else if Formula.is_true phi then `True
      else `Undecided
    with exn_ when not (Common.Timer.is_async exn_) -> `Undecided

  (* [judge] and, where it is undecided, a solver: [sat] asked of the instance
     with the model's values substituted ([`Unsat] makes it [`False]) and then
     of its negation ([`Unsat] makes it [`True]).  What the substitution leaves
     open -- a model element's name, a variable the model leaves out, a term
     the theory leaves open -- is left to the solver, so an [`Unsat] holds for
     every value of it, the model's included: sound in both directions as far
     as [sat]'s [`Unsat] is.  For an atom the simplifier does not decide: an
     application of a recursive function, or a quantifier over the model's
     arrays. *)
  let judge_by_solver ~sat (model : model) phi =
    match judge model phi with
    | (`True | `False) as r -> r
    | `Undecided -> (
        try
          let phi = instantiate model phi in
          match sat phi with
          | `Unsat -> `False
          | _ -> (
              match sat (Formula.mk_neg phi) with
              | `Unsat -> `True
              | _ -> `Undecided)
        with exn_ when not (Common.Timer.is_async exn_) -> `Undecided)

  (* [run ~stop ~ask ~judge ?aside atoms] is [(proved, dropped)]: [proved]
     the atoms of [atoms] whose conjunction one question [ask] proved,
     [dropped] the atoms of [atoms] and [aside] a countermodel [judge]d
     [`False].  Every other atom is left to the caller's per-atom question.

     Contract, for a clause question [body => head] whose [body] is fixed:
     [ask held] proves [body => /\ held] ([`Proved]) or gives a model of
     [body /\ ~(/\ held)] ([`Refuted m]).  Then every atom of [proved] has a
     valid per-atom question (its head is implied by the conjunction), and
     every atom of [dropped] has a per-atom question refuted by the very model
     that dropped it: the model satisfies [body], whichever conjunction it
     was found for, and the atom is false in it.  So when every per-atom
     question decides, keeping [proved], dropping [dropped] and asking the
     rest one by one keeps exactly the atoms the per-atom questions alone
     would keep.

     The loop: ask the held atoms; on a refutation judge the held atoms and
     the ones set aside, drop the ones judged [`False], and ask the rest of
     the held ones again; when a countermodel drops nothing but judges some
     held atom [`True] and some [`Undecided], set the undecided ones aside
     (their own questions decide them) and ask the [`True] ones again; stop
     on a proof, an undecided question, a countermodel that drops nothing
     otherwise, one held atom or fewer, or [stop ()].  [prejudge m atoms]
     is called once per countermodel, with every atom about to be judged
     against it, before [judge]: a place to judge them all at once.  [aside] (default
     none) are atoms never put in a conjunction, only judged against each
     countermodel: atoms whose questions are expensive in a conjunction, such
     as existentials over sequences. *)
  let run ?(aside = []) ?(prejudge = fun _ _ -> ()) ~stop ~ask ~judge atoms =
    let rec loop held aside dropped =
      if List.length held <= 1 || stop () then ([], dropped)
      else
        match ask held with
        | `Proved -> (held, dropped)
        | `Undecided -> ([], dropped)
        | `Refuted model ->
            prejudge model (held @ aside);
            let split atoms =
              let judged = List.map atoms ~f:(fun a -> (a, judge model a)) in
              let with_ v =
                List.filter_map judged ~f:(fun (a, r) ->
                    if Stdlib.(r = v) then Some a else None)
              in
              (with_ `False, with_ `True, with_ `Undecided)
            in
            let f, t, u = split held in
            let af, at, au = split aside in
            let aside = at @ au and dropped = f @ af @ dropped in
            if not (List.is_empty f) then loop (t @ u) aside dropped
            else if (not (List.is_empty t)) && not (List.is_empty u) then
              loop t (u @ aside) dropped
            else ([], dropped)
    in
    loop atoms aside []
end

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
     [weaken_unreturnable_keep_cells] asks for them to be asked *)
  let () =
    if
      PCSatCommon.WeakenedQuery.leaves_cells_undecided
        ~weaken:config.weaken_unreturnable_queries
        ~keep_cells:config.weaken_unreturnable_keep_cells
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
      config.weaken_unreturnable_queries
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
     [record_head_witnesses] is on, so that the model a counterexample is built
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
     [houdini_budget_ms] ([None] at every other time, so nothing below changes
     a question asked outside the pre-pass).  While it is set, every solver
     question the validator asks -- the pre-pass's own and its final check's --
     is given at most what is left of it ([cap_timeout]), a question with no
     budget of its own included; a validation query of the default
     configuration has none, and one of the final check's questions ran past
     70 s and out of memory on an input the loop answers in 2 s. *)
  let houdini_deadline : Time_ns.t option ref = ref None

  (* [houdini_atom_countermodel_drops]: while one atom's question of the
     fixed point is asked, the question as it reaches
     [check_clause_nonparam_smt] (compared by physical identity) and the
     judge of the clause's atoms still to be asked, which gives the positions
     of those a model of the question's negation makes false; and the
     positions a countermodel of that question refuted, once it has been
     answered.  Both are cleared by the fixed point after each question. *)
  let houdini_pending_judge : (Formula.t * (model -> int list)) option ref =
    ref None

  let houdini_judged_drops : int list option ref = ref None

  (* how many atoms a reused countermodel dropped without a question of their
     own; read by the tests *)
  let houdini_atom_model_drops = ref 0

  (* how many questions of the fixed point were proved against the body held
     once per clause ([houdini_shared_body_session]); read by the tests *)
  let houdini_shared_body_proofs = ref 0

  (* how many were refuted there by a model every conjunct set aside holds
     under; read by the tests *)
  let houdini_shared_body_refutations = ref 0

  (* set by [houdini_shared_body_session] for the next question only, when
     the fixed point's solver has just found the body's other conjuncts and
     the head's negation satisfiable by a model that does not extend: the
     weakened question asks exactly that again, so the question goes straight
     to the forked copy *)
  let houdini_skip_weakened_once = ref false

  (* the judge of [houdini_pending_judge] applied to [model], when [phi] is
     the very question it was set for; an exception of the judge drops
     nothing *)
  let judge_pending_atoms phi model =
    match !houdini_pending_judge with
    | Some (key, judge) when phys_equal key phi -> (
        try Some (judge model)
        with exn_ when not (Common.Timer.is_async exn_) -> Some [])
    | _ -> None

  (* [true] while the pre-pass's final check of its fixed point runs, for
     [houdini_final_seq_axiom_first] *)
  let houdini_in_final = ref false

  (* the milliseconds left before the deadline, [None] when none is set *)
  let houdini_remaining_ms () =
    Option.map !houdini_deadline ~f:(fun d ->
        Time_ns.Span.to_int_ms (Time_ns.diff d (Common.Clock.now_ns ())))

  let houdini_budget_spent () =
    match houdini_remaining_ms () with Some r -> r <= 0 | None -> false

  (* spent, or so nearly that the question just asked was cut short by it:
     a solver can give up a few milliseconds before the budget it was given *)
  let houdini_budget_nearly_spent () =
    match houdini_remaining_ms () with Some r -> r <= 100 | None -> false

  (* [t] itself when no deadline is set; otherwise the smaller of [t] and the
     remainder (at least 1 ms, since a solver budget of 0 means none).
     A caller's [Some 0] is unbounded, just like [None], so it must take the
     remainder rather than winning the numeric minimum. *)
  let cap_timeout (t : int option) =
    match houdini_remaining_ms () with
    | None -> t
    | Some r -> (
        let r = max 1 r in
        match t with
        | Some t when t <> 0 && t <= r -> Some t
        | _ -> Some r)

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
     its sequence reads of concatenations split with [split_seq_reads] *)
  let negation_asked phi =
    let neg_phi = Evaluator.simplify @@ Formula.mk_neg phi in
    if config.split_seq_reads then Evaluator.rewrite_seq_read_over_concat neg_phi
    else neg_phi

  (* how many satisfiable answers of a forked copy were asked again in this
     process for their model; read by the tests *)
  let forked_sat_reasks = ref 0

  (* how many counterexample queries were asked in this process in a context
     of their own ([fresh_context_quantified_queries]); read by the tests *)
  let fresh_context_asked = ref 0

  (* The in-process counterexample query [neg_phi] of a clause.  Contract:
     the answer of [Z3interface.check_sat] on [neg_phi] with [timeout]; with
     [fresh_context_quantified_queries] and a quantifier in [neg_phi], asked
     as the process-wide [AlwaysFresh] policy asks it
     ([Z3interface.check_sat_fresh]: a context of its own, the negation normal
     form of [neg_phi], which is equivalent to it, and the definitions it
     reaches), so a model is a model of [neg_phi] and [`Unsat] means [neg_phi]
     has none; a shape that check refuses ([may_not_return]) and everything
     quantifier-free are asked in the pooled context as before. *)
  let ask_counterexample_query ~timeout fenv neg_phi =
    match
      if
        config.fresh_context_quantified_queries
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

  (* [ask_counterexample_query], with [scoped_first_quantified_validation]
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
        ~enabled:config.scoped_first_quantified_validation
        ~scoped_ms:config.scoped_first_quantified_validation_ms ~timeout ~id
        fenv [ neg_phi ] ~ask:(fun () ->
          ask_counterexample_query ~timeout fenv neg_phi)
    in
    res

  (* how many undecided clause questions were asked of cvc5
     ([clause_check_cvc5_retry_ms]), and how many of them it proved valid;
     read by the tests *)
  let cvc5_retry_asked = ref 0

  let cvc5_retry_proved = ref 0

  (* how many undecided clause questions were asked again in the axiom form
     ([clause_check_seq_axiom_fallback]); read by the validation dump *)
  let clause_check_seq_axiom_asked = ref 0

  (* [true] while a validation question whose axiom form was already asked
     first ([clause_check_axiom_first_when_proved]) is asked natively, so that
     the axiom form is not asked a second time *)
  let suppress_clause_axiom_fallback = ref false

  (* [verdict_only]: the caller reads only which of [`Sat], [`Unsat],
     [`Timeout] and [`Unknown] the answer is, never a model, so a forked
     copy's [`Sat] is returned with an empty model instead of being asked
     again here; it is ignored when the model is needed for a witness
     ([record_cell_witnesses]) *)
  let check_clause_nonparam_smt ?(timeout = None) ?(verdict_only = false) fenv
      phi =
    let timeout = cap_timeout timeout in
    let neg_phi =
      Common.PhaseTime.with_phase "negate" (fun () -> negation_asked phi)
    in
    let neg_phi, witness_vars =
      if config.record_cell_witnesses || config.record_head_witnesses then
        skolemize_positive_existentials neg_phi
      else (neg_phi, [])
    in
    if config.record_head_witnesses then note_head_witness_vars witness_vars;
    Debug.print
    @@ lazy (sprintf "[check valid -> sat] %s" @@ Formula.str_of neg_phi);
    let weakened =
      if
        config.weaken_unreturnable_queries
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
    (* [houdini_weaken_unreturnable]: the weakened question before the killed
       copy; [None] from it leaves the question to the copy as before *)
    let skip_weakened = !houdini_skip_weakened_once in
    houdini_skip_weakened_once := false;
    let weakened =
      if
        Option.is_none weakened && houdini_fork
        && config.houdini_weaken_unreturnable
        && not skip_weakened
      then
        Common.PhaseTime.with_phase "weakened" (fun () ->
            weaken_and_model_check ~timeout fenv neg_phi)
      else weakened
    in
    (* [houdini_final_seq_axiom_first]: in the pre-pass's final check, a
       clause over sequences is first asked in the axiom form, and a proof
       there is the answer ([`Unsat]: no model of the negation exists);
       otherwise the question is asked as before, without the fallback
       asking the axiom form a second time *)
    let axiom_first =
      config.houdini_final_seq_axiom_first && !houdini_in_final
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
       still to be asked ([houdini_atom_countermodel_drops]) *)
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
      let fork_wanted =
        config.fork_unreturnable_queries
        && (Z3Smt.Z3interface.may_not_return neg_phi
           || config.fork_quantified_queries
              && not (Formula.is_quantifier_free neg_phi))
      in
      let pointwise =
        if config.array_pointwise_elim && not houdini_fork then
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
      if config.arrays_as_functions && (not houdini_fork) && not fork_wanted
      then (
        let res, outcome =
          Z3Smt.Z3interface.check_sat_arrays_as_functions ~id ~timeout fenv
            [ neg_phi ]
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
        res)
      else if houdini_fork || fork_wanted then (
        (* no Z3 timer in the copy: the kill is the budget, and the thread
           that serves a Z3 timer does not exist in a forked process *)
        let ms =
          if houdini_fork then Option.value timeout ~default:10000
          else
            PCSatCommon.ForkedQuery.kill_ms
              ~kill_ms:config.fork_unreturnable_kill_ms ~timeout
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
                    ~fresh_solver:(houdini_fork && config.houdini_fork_fresh_context)
                    fenv [ neg_phi ]
                with
                | `Sat m ->
                    (* [houdini_atom_countermodel_drops]: the copy holds the
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
    (* [clause_check_seq_axiom_fallback]: an undecided question is asked once
       more as the validity of [phi] in the axiom form; only a proof is read,
       as [`Unsat] (no model of the negation exists), so a decided answer and
       an unproved one are left as they were *)
    let res =
      match res with
      | (`Timeout | `Unknown _)
        when config.clause_check_seq_axiom_fallback && (not axiom_first)
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
    (* [clause_check_cvc5_retry_ms]: an undecided question asked of cvc5 as
       the validity of [phi]; only its [unsat] is read *)
    let res =
      match (res, config.clause_check_cvc5_retry_ms) with
      | (`Timeout | `Unknown _), Some ms when ms > 0 ->
          incr cvc5_retry_asked;
          let t0 = Common.PhaseTime.now () in
          let proved =
            Common.PhaseTime.with_phase "cvc5-retry" (fun () ->
                PCSatCommon.Cvc5Proof.valid_within ~site:"validation"
                  ~ms:(cap_ms ms) ~id fenv phi)
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
          if config.diversify_sequences then
            Evaluator.simplify (drop_vacuous_binders neg_phi)
          else neg_phi
        in
        let arrays_ok =
          config.diversify_arrays && Formula.is_quantifier_free neg_phi
        in
        let sequences_ok =
          config.diversify_sequences && Formula.is_quantifier_free neg_phi_seq
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
                              && config.diversify_at_clause_read_indices
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
                      "the counterexample's array is constant at %d place(s) and its sequence uninformative at %d;                        asking again for one that varies"
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
    (* [diversify_scalar_counterexamples]: a counterexample whose integers lie
       close to the last one asked for the same variables is asked again with
       a Manhattan distance required; the first model is kept unless the
       second query answers [Sat], so this only chooses which counterexample
       is used.  Not asked for a verdict-only caller (it reads no model), nor
       on a shape [may_not_return] refuses. *)
    let res =
      match res with
      | `Sat model
        when config.diversify_scalar_counterexamples && (not verdict_only)
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
    (match (res, witness_vars) with
    | _, [] -> ()
    | `Sat model, _ ->
        List.iter model ~f:(fun ((x, _s), v) ->
            match v with
            | Some t when List.Assoc.mem witness_vars ~equal:Stdlib.( = ) x -> (
                match Term.value_of (Evaluator.simplify_term t) with
                | Value.Int z ->
                    if config.record_cell_witnesses then CellQual.record_witness z
                | _ -> ()
                | exception exn_ when not (Common.Timer.is_async exn_) -> ())
            | _ -> ())
    | _ -> ());
    res

  (* The budget of a validation query over [phi], the clause with the candidate
     substituted: [smt_timeout_quantified] where [phi] still contains a
     quantifier (the smaller of the two when both are set), [smt_timeout]
     otherwise. *)
  let timeout_for phi =
    if Formula.is_quantifier_free phi then config.smt_timeout
    else
      match (config.smt_timeout, config.smt_timeout_quantified) with
      | Some a, Some b -> Some (min a b)
      | None, q -> q
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
  (* [true] exactly while one question runs under [houdini_seq_question_ms]:
     the asks of [check_clause_readback] then stop the route once the
     narrowed deadline is spent ([Question_budget_spent]) *)
  let in_capped_question = ref false

  (* [true] exactly while [houdini_fixed_point] runs: [houdini_seq_question_ms]
     caps its questions only, never the final check's, where a question cut
     short would reject the whole fixed point and send the pre-pass into
     another round instead of dropping one atom *)
  let in_houdini_fixed_point = ref false

  (* [true] exactly while a per-atom question of [houdini_fixed_point] is
     asked (not a conjunction question of [houdini_drop_by_model], not the
     final check), for [houdini_atom_questions_prove_only] *)
  let in_houdini_atom_question = ref false

  (* [true] exactly while a conjunction question of [houdini_drop_by_model]
     is asked, for [houdini_drop_by_model_conjunction_ms] *)
  let in_houdini_conjunction_question = ref false

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
        | _ when config.retry_undecided_readback_forms -> (
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
          if config.split_seq_reads then
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
    (* [houdini_atom_questions_prove_only]: a per-atom question of the
       pre-pass's fixed point keeps its atom only when proved, a refutation
       and an undecided answer both dropping it, so its refuters are not
       built: building one length-bounded refuter is not a solver call and is
       cut short by no budget (6 and 8.5 s on two such questions) *)
    let prove_only =
      config.houdini_atom_questions_prove_only && !in_houdini_atom_question
    in
    SeqInstantiation.decide_clause
      ~subst_definitions:config.readback_subst_definitions ~ask_form ~ask_full
      ~ask_pinned:
        (if prove_only then fun _ -> `Unknown "refuters not built"
         else ask_pinned)
      ~bounded:(if prove_only then [] else bounded)
      phi

  let binds_sequence_existentially =
    HoudiniCandidates.binds_sequence_existentially
      ~arrays:config.houdini_array_existentials

  (* [true] exactly while [houdini_outcome] runs (the fixed point and its
     final check) with [houdini_seq_instantiation] on *)
  let in_houdini_seq_instantiation = ref false

  (* the sequence-existential questions asked first as plain questions under
     [houdini_seq_plain_first_ms], and how many of them that decided (asked,
     decided); never reset here, read by the tests *)
  let houdini_plain_first_counts = (ref 0, ref 0)

  (* the sequence-existential questions that ran under
     [houdini_seq_question_ms] and how many of them its budget cut short
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
     and inside it without [houdini_seq_instantiation], exactly as before.
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
  (* [houdini_question_mode] other than [Plain_first]: a sequence-existential
     question of the pre-pass's fixed point asked by two searches, within the
     question's cap (the pre-pass's deadline, narrowed by
     [houdini_seq_question_ms], or [houdini_drop_by_model_conjunction_ms] for
     a conjunction question, as without the field):
     - the plain question ([plain]): the question itself, asked of the solver
       for a slice;
     - the route ([route]): the witness-instantiation route, in a forked copy
       killed at the end of its slice, asked for a proof only.
     [Switch] asks the plain question for [houdini_seq_plain_first_ms] (the
     whole cap when that is unset), then the route for the rest; [Dovetail]
     alternates them in slices doubling from [houdini_dovetail_start_ms];
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
  let houdini_instr_pass = ref 0
  let houdini_instr_clause = ref 0
  let houdini_instr_question = ref 0
  let houdini_instr_premise : Formula.t Lazy.t option ref = ref None

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
    let t0 = Core_unix.gettimeofday () in
    List.iter ps ~f:(fun piece ->
        ignore
          (SeqInstantiation.instantiate ?max_nodes:!SeqInstantiation.piece_max_nodes
             (SeqInstantiation.prepare_piece piece)
            : Formula.t));
    ( Core_unix.gettimeofday () -. t0,
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
      (match config.houdini_drop_by_model_conjunction_ms with
      | Some ms when !in_houdini_conjunction_question -> Some ms
      | _ -> config.houdini_seq_question_ms)
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
        match config.houdini_question_mode with
        | Config.Plain_first -> assert false
        | Switch -> (
            let first =
              match config.houdini_seq_plain_first_ms with
              | Some ms -> slice ms
              | None -> slice Int.max_value
            in
            match plain first with
            | Some r -> r
            | None -> if left () <= 0 then `Timeout else decided (route (slice Int.max_value)))
        | Dovetail ->
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
            go (Int.max 1 config.houdini_dovetail_start_ms)
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
      config.instantiate_readback_universals
      && (not (Formula.is_quantifier_free phi))
      && reads_sequence phi
    then
      Common.PhaseTime.with_phase "readback" (fun () ->
          check_clause_readback ~timeout fenv phi)
    else if
      !in_houdini_seq_instantiation
      && !in_houdini_fixed_point
      && (match config.houdini_question_mode with
         | Config.Plain_first -> false
         | _ -> true)
      && binds_sequence_existentially phi
    then
      Common.PhaseTime.with_phase "question-mode" (fun () ->
          houdini_two_searches ~timeout ~verdict_only fenv phi)
    else if !in_houdini_seq_instantiation && binds_sequence_existentially phi
    then
      let plain =
        match
          match config.houdini_conjunction_plain_first_ms with
          | Some ms when !in_houdini_conjunction_question -> Some ms
          | _ -> config.houdini_seq_plain_first_ms
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
                (match config.houdini_drop_by_model_conjunction_ms with
                | Some ms when !in_houdini_conjunction_question -> Some ms
                | _ -> config.houdini_seq_question_ms)
                (fun () ->
                  let route () =
                    check_clause_readback ~guard_both_ways:false ~ladder:true
                      ~timeout fenv phi
                  in
                  (* [houdini_atom_questions_prove_only]: a per-atom question
                     needs only whether the route proves it, so the route runs
                     in a forked copy killed when the deadline is reached,
                     which bounds the building of its forms too *)
                  match houdini_remaining_ms () with
                  | Some r
                    when config.houdini_atom_questions_prove_only
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

  (* [houdini_memo_questions]: the decided answers of the pre-pass's
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

  (* With [houdini_memo_questions], inside the pre-pass (its deadline set),
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
    | Some _ as deadline when config.houdini_memo_questions ->
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

  let check_clause_param_smt ?(timeout = None) fenv params_senv uni_senv phi =
    let qphi =
      Formula.forall
        (Map.Poly.to_alist @@ Logic.to_old_sort_env_map uni_senv)
        phi
    in
    let timeout = cap_timeout timeout in
    match Z3Smt.Z3interface.check_sat ~id ~timeout fenv [ qphi ] with
    | `Sat _model ->
        `Unsat (*ToDo: show model for parameters of the candidate solution *)
    | _ ->
        (* unsat, unknown, timeout*)
        let sub = Logic.to_old_dummies params_senv in
        check_clause_nonparam_smt ~timeout fenv (Formula.subst sub phi)

  let solve =
    let module Z3interface =
      Z3Smt.Z3interfaceNew.Make (Z3Smt.Z3interfaceNew.ExtTerm) in
    fun senv phi -> Z3interface.check_sat [ phi ] senv (Z3.mk_context [])

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
     ([clause_check_axiom_first_when_proved]) *)
  let axiom_proved_clauses : (string, unit) Hashtbl.t = Hashtbl.create (module String)

  let clause_key clause = Md5.to_hex (Md5.digest_string (Logic.ExtTerm.str_of clause))

  (* the problem clauses whose validation question was last left undecided
     ([defer_undecided_clauses]) *)
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
     ([validation_by_pieces]) *)
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
        let rec go undecided = function
          | [] -> if undecided then `Timeout else `Unsat
          | p :: rest -> (
              if proved_by_axioms p then go undecided rest
              else
                match native p with
                | `Unsat -> go undecided rest
                | `Sat m -> `Sat m
                | _ -> go true rest)
        in
        let res =
          Common.PhaseTime.with_phase "by-pieces" (fun () -> go false pieces)
        in
        (match res with
        | `Unsat | `Sat _ -> incr (snd by_pieces_counts)
        | _ -> ());
        Some res

  let check_validation_clause_ordinary ~key ~timeout fenv phi =
    if
      config.clause_check_axiom_first_when_proved
      && config.clause_check_seq_axiom_fallback
      && Hashtbl.mem axiom_proved_clauses (Lazy.force key)
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
        when config.clause_check_axiom_first_when_proved
             && !clause_check_seq_axiom_asked > asked_before ->
          Hashtbl.set axiom_proved_clauses ~key:(Lazy.force key) ~data:()
      | _ -> ());
      res

  (* [check_validation_clause_ordinary], and with [validation_by_pieces] the
     piece route: after an undecided ordinary answer for a quantified
     question, or first for a clause the piece route decided before (then the
     ordinary route only when the pieces leave it undecided).  Every answer is
     one of the two routes', each sound. *)
  let check_validation_clause_unmemoised ~key ~timeout fenv phi =
    match config.validation_by_pieces with
    | Some (axiom_ms, native_ms) when not (Formula.is_quantifier_free phi) -> (
        let by_pieces () =
          check_by_pieces ~axiom_ms ~native_ms fenv phi
        in
        let decided = function `Unsat | `Sat _ -> true | _ -> false in
        let k = Lazy.force key in
        let first =
          if Hashtbl.mem pieces_first_clauses k then by_pieces () else None
        in
        match first with
        | Some r when decided r -> r
        | Some _ ->
            Hashtbl.remove pieces_first_clauses k;
            check_validation_clause_ordinary ~key ~timeout fenv phi
        | None -> (
            let r = check_validation_clause_ordinary ~key ~timeout fenv phi in
            if decided r then r
            else
              match by_pieces () with
              | Some r' when decided r' ->
                  Hashtbl.set pieces_first_clauses ~key:k ~data:();
                  r'
              | _ -> r))
    | _ -> check_validation_clause_ordinary ~key ~timeout fenv phi

  (* [validation_memo_alpha]: the decided-valid validation questions of this
     solve, keyed by the question with its bound variables renamed in order of
     occurrence ([alpha_key]); with [validation_memo_undecided], also the
     undecided ones with the budget they were asked under *)
  let validation_memo : (Formula.t, [ `Valid | `Undecided of int option ]) Hashtbl.t =
    Hashtbl.PolyDeep.create ()

  (* how many validation questions the memo answered; read by the tests *)
  let validation_memo_hits = ref 0

  (* [phi] with every bound variable renamed by a counter in traversal order,
     its free variables kept: two questions differing only in bound names get
     the same key, and two with different free variables or sorts do not *)
  let alpha_key phi =
    let n = ref 0 in
    Formula.aconv_tvar_norm
      (fun () ->
        incr n;
        Ident.Tvar (sprintf "#vmemo%d" !n))
      phi

  (* Contract: as [check_validation_clause_unmemoised], except that with
     [validation_memo_alpha] a question whose [alpha_key] an earlier question
     proved valid is answered [`Unsat] unasked (and, with
     [validation_memo_undecided], one an earlier question left undecided under
     the same budget is answered [`Timeout] unasked). *)
  let check_validation_clause ~key fenv phi =
    let timeout = timeout_for phi in
    if not config.validation_memo_alpha then
      check_validation_clause_unmemoised ~key ~timeout fenv phi
    else
      let k = alpha_key phi in
      match Hashtbl.find validation_memo k with
      | Some `Valid ->
          Int.incr validation_memo_hits;
          `Unsat
      | Some (`Undecided t)
        when config.validation_memo_undecided && Option.equal Int.equal t timeout ->
          Int.incr validation_memo_hits;
          `Timeout
      | _ ->
          let res = check_validation_clause_unmemoised ~key ~timeout fenv phi in
          (match res with
          | `Unsat -> Hashtbl.set validation_memo ~key:k ~data:`Valid
          | `Sat _ -> ()
          | _ -> Hashtbl.set validation_memo ~key:k ~data:(`Undecided timeout));
          res

  (* With [COAR_DUMP_VALIDATION_QUESTIONS=dir] in the environment, each
     non-parametric clause question of validation is recorded: one line of
     [dir/meta.tsv] (the question's number and process, seconds since the
     first, the digest of its printed form, its size, whether it is
     quantifier-free, reads a sequence and is one the solver may not return
     on, the outcome, the seconds it took and whether it reached the
     sequence-axiom fallback, and the digest of the problem clause it
     comes from), its printed form once per digest as
     [dir/phi_<digest>.txt], and every solver check it made as SMT-LIB under
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
        let clause_digest =
          Md5.to_hex (Md5.digest_string (Logic.ExtTerm.str_of clause))
        in
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
     [unknown:<reason>]), and once more under [.../slow] when it took a second
     or more, so that a run whose validation time went to exhausted budgets
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
        if Float.(dt >= 1.) then Common.PhaseTime.add (row ^ "/slow") dt
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
    (* [defer_undecided_clauses]: the clauses an earlier round left
       undecided go last, and are skipped once a clause before them gave a
       counterexample *)
    let cls_first, cls_deferred =
      let l = Set.to_list cls_nonparam in
      if config.defer_undecided_clauses then
        List.partition_tf l ~f:(fun ((_, clause, _, _, _), _) ->
            not (Hashtbl.mem undecided_clauses (clause_key clause)))
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
      if config.defer_undecided_clauses && not skipped then (
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
    let cls_param =
      Set.to_list cls_param
      |> List.classify (fun ((_, _, senv1, _, _), _) ((_, _, senv2, _, _), _) ->
          Fn.non Set.is_empty
          @@ Set.inter (Map.Poly.key_set senv1) (Map.Poly.key_set senv2))
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
                        (if config.generalise_invented_values then
                           Some (Lazy.force stated_literals)
                         else None)
                      ~partial_model:config.partial_model_examples
                      ~partial_seq_elements:
                        (config.partial_model_seq_elements
                        || config.partial_model_seq_elements_goal_only)
                      ~partial_seq_elements_goal_only:
                        config.partial_model_seq_elements_goal_only
                      ~group_equal:config.partial_model_group_equal_values
                      ~settle_pure:config.partial_model_settle_pure
                      (PCSP.Problem.senv_of APCSP.problem)
                      config.parametric_examples (uni_senv, phi_clause) model
                  in
                  let exs =
                    Set.Poly.map exs
                      ~f:
                        (ExClause.simplify_wfpvs
                           (PCSP.Problem.wfpvs_of APCSP.problem))
                  in
                  (* the goal clause's own read indices, beside the example
                     and keyed by its atoms; only a goal clause is recorded
                     here, so that every record is the whole of what the
                     clause's refutation reads *)
                  (if config.record_goal_reads then
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
                  (if config.record_head_witnesses then
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
                    if config.record_premise_instances then
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
                    if not config.fact_clause_examples then (exs, sub)
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
                      config.partial_model_fact_examples
                      && config.parametric_examples
                      && (not config.partial_model_examples)
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

  let receive_bounds vs =
    match PCSP.Problem.messenger_of APCSP.problem with
    | None -> ()
    | Some messenger ->
        let add =
          VersionSpace.add_bound_as_learned_clause ~print:Debug.print id
            APCSP.problem vs
        in
        Common.Messenger.receive_all_infos_with messenger id ~filter:(function
          | PCSP.Problem.(LowerBounds _ | UpperBounds _) -> true
          | _ -> false)
        |> List.iter ~f:(function
          | _, PCSP.Problem.LowerBounds bounds ->
              Map.Poly.iteri bounds ~f:(fun ~key ~data -> add key data false)
          | _, PCSP.Problem.UpperBounds bounds ->
              Map.Poly.iteri bounds ~f:(fun ~key ~data -> add key data true)
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
                (*ToDo: this case is necessary because [partial_sol_targets_of pfwcsp] is empty if [gen_extra_partial_sols] is false*)
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

  (* A Houdini-style first candidate (after Flanagan and Leino, "Houdini, an
     Annotation Assistant for ESC/Java", FME 2001) from the candidate atoms the
     input declared ([(set-info :candidates ...)]) and, with
     [houdini_extracted_qualifiers] or [houdini_defined_body_atoms], atoms the
     tool generates itself ([houdini_candidates]): each unknown starts as the
     conjunction of its candidate atoms (an unknown with none as [true]), and an
     atom is dropped while some clause, with the current conjunctions in its
     body, is not valid with that atom alone in its head.  The loop stops when a
     pass drops nothing; since every pass but the last drops an atom, it makes
     at most (atoms + 1) passes, each asking at most one question per remaining
     atom per (clause, head atom) pair.  Where the atoms come from does not
     matter to what follows: a generated atom is kept only as a declared one
     is, by the same questions.  A question the solver
     leaves undecided (budget, [unknown]) drops the atom, as a refutation would.
     With [houdini_budget_ms], this function runs under the pre-pass's one
     wall-clock budget ([with_houdini_deadline]; [houdini_outcome]'s final
     check shares it): candidate generation stops when it runs out, each
     question is given at most what is left of it, and once it is spent no
     question is asked and this function returns [None] -- every atom still
     unconfirmed would count as undecided and be dropped, which leaves nothing
     to try.

     The fixed point is inductive for the clauses with an unknown in the head;
     it is a solution only if the goal clauses hold as well, and that is not
     assumed: this function returns the fixed point unchecked, and
     [houdini_outcome] reports it as a solution only after
     [find_all_counterexamples] has checked it against every clause, exactly as
     a synthesized candidate is checked.  So the pre-pass cannot make an answer
     wrong; what it can do is answer early, hand the check's counterexamples on
     as ordinary examples, or cost the questions above and change nothing.
     [None] means there is nothing to try.

     Each question is the validator's own [check_clause_nonparam], with its
     budgets and its guards against queries that may not return.  Only problems
     whose unknowns are all of the ordinary kind are tried: [true] and a
     conjunction of atoms carry no certificate for a well-foundedness or a
     totality demand. *)
  (* whether the pre-pass generates candidates of its own; a function,
     since a reconstruction pass run by the solver after this module is
     made can switch the reconstructed-function family on *)
  let houdini_generates () =
    Option.is_some config.houdini_extracted_qualifiers
    || config.houdini_defined_body_atoms > 0
    || config.houdini_rec_fun_apps > 0
    || Atomic.get PCSatCommon.RecFunReconstruct.qual_limit > 0
    || config.houdini_frame_equations > 0
    || config.houdini_contract_memberships > 0
    || config.houdini_oriented_inequalities > 0
    || config.houdini_quantified_facts > 0
    || config.houdini_relation_inclusions > 0
    || config.houdini_exists_memberships > 0
    || config.houdini_guarded_frame_equations > 0
    || config.houdini_empty_guarded_frames > 0
    || config.houdini_length_sums > 0
    || config.houdini_last_element_equations > 0
    || config.houdini_affine_elements > 0
    || config.houdini_prefix_elements > 0
    || config.houdini_three_term_equations > 0
    || config.houdini_guarded_orders > 0

  (* The atoms the pre-pass generates for each unknown, over [x1 ... xn] (the
     names every qualifier of an unknown is written over), before
     [HoudiniCandidates.merge] filters and caps them.  Computed when the
     pre-pass first asks and kept, from the problem this validator was built with and
     the process-global definitions the parser registered -- never from the
     synthesizer's state -- so it is the same whether or not the synthesizer
     has extracted its qualifiers by then (the pre-pass can run before the
     first synthesis).  A generator that raises gives no atom for that
     unknown.  [stop] is asked before each unknown, between its generators
     and inside the generators' loops; once it holds the generation is
     abandoned, [None] is returned and nothing is kept, so a later call
     starts again.  The extraction ([houdini_extracted_qualifiers]) is one
     call into the qualifier generator and is not interrupted inside.  The
     atoms are kept per class (the name of the switch that
     produced them), both polarities of each, for the census below; they live
     here and in the pre-pass's questions only, and never reach the
     synthesizer's qualifiers or the problem's declared atoms. *)
  (* whether the pre-pass runs in two rounds
     ([houdini_inclusions_second_round] with both inclusion counts positive) *)
  let houdini_two_rounds =
    config.houdini_inclusions_second_round
    && config.houdini_relation_inclusions > 0
    && config.houdini_max_inclusion_candidates > 0

  (* whether the round being run generates the inclusion family; [false] only
     inside round 1 of a two-round pre-pass, where the family is the empty
     list it is with [houdini_relation_inclusions = 0] *)
  let houdini_with_inclusions = ref true

  (* [Some (with_inclusions, m)]: the atoms generated, and whether [m] holds
     the inclusion family or has it empty *)
  let houdini_generated_cache = ref None

  let houdini_inclusion_family ~stop args =
    HoudiniCandidates.inclusions ~stop ~limit:config.houdini_relation_inclusions
      ~skip_constructor_equations:
        (config.houdini_inclusions_skip_constructor_equations
        && config.houdini_frame_equations > 0)
      ~defs:(LogicOld.get_inlined_defs ()) args

  let houdini_print_family key args name atoms =
    if not (List.is_empty atoms) then
      Debug.print
      @@ lazy
           (sprintf "[houdini] %s over %s: %s (%d): %s"
              (Ident.name_of_tvar key)
              (String.concat_map_list ~sep:"," args
                 ~f:(fst >> Ident.name_of_tvar))
              name (List.length atoms)
              (String.concat_map_list ~sep:" | " atoms ~f:Formula.str_of))

  (* the parameters of [key] its loops pass on unchanged, for
     [houdini_quantified_facts_frame_only] ([[]] with the switch off) *)
  let houdini_frame_args key (args : sort_env_list) =
    if not config.houdini_quantified_facts_frame_only then []
    else
      let pos =
        HoudiniCandidates.frame_positions
          (Set.to_list (PCSP.Problem.clauses_of APCSP.problem))
          key
      in
      let frame = List.filteri args ~f:(fun i _ -> List.mem pos i ~equal:( = )) in
      Debug.print
      @@ lazy
           (sprintf "[houdini] %s: frame parameters %s" (Ident.name_of_tvar key)
              (String.concat_map_list ~sep:"," frame ~f:(fst >> Ident.name_of_tvar)));
      frame

  let houdini_generated_atoms ~stop =
    let want = !houdini_with_inclusions in
    match !houdini_generated_cache with
    | Some (w, m) when Bool.equal w want -> Some m
    | Some (true, m) ->
        (* the inclusions held but not wanted: the family emptied *)
        Some
          (Map.Poly.map m ~f:(fun (args, fams) ->
               ( args,
                 List.map fams ~f:(fun (name, atoms) ->
                     if String.equal name "inclusion" then (name, [])
                     else (name, atoms)) )))
    | Some (false, m) -> (
        (* round 2 after round 1: only the inclusion family is generated, in
           its place among the families, so the atoms are those a one-round
           generation gives; a generator that raises gives no atom for that
           unknown, as it does there *)
        match
          Map.Poly.mapi m ~f:(fun ~key ~data:(args, fams) ->
              HoudiniCandidates.poll stop;
              if List.is_empty fams then (args, fams)
              else
                try
                  let inc = houdini_inclusion_family ~stop args in
                  houdini_print_family key args "inclusion" inc;
                  ( args,
                    List.map fams ~f:(fun (name, atoms) ->
                        if String.equal name "inclusion" then (name, inc)
                        else (name, atoms)) )
                with
                | HoudiniCandidates.Budget_spent as exn_ -> raise exn_
                | exn_ when not (Common.Timer.is_async exn_) ->
                    Debug.print
                    @@ lazy
                         (sprintf "[houdini] no generated atom for %s: %s"
                            (Ident.name_of_tvar key) (Exn.to_string exn_));
                    (args, []))
        with
        | m ->
            houdini_generated_cache := Some (true, m);
            Some m
        | exception HoudiniCandidates.Budget_spent ->
            Debug.print
            @@ lazy "[houdini] budget spent while generating candidates";
            None)
    | None -> (
       let poll = HoudiniCandidates.poll in
       let senv = PCSP.Problem.senv_of APCSP.problem in
       let args_of data =
         sort_env_list_of_sorts
         @@ List.map (Logic.Sort.args_of data) ~f:Logic.ExtTerm.to_old_sort
       in
       let extracted =
         match config.houdini_extracted_qualifiers with
         | None -> fun _ _ -> []
         | Some gcfg ->
             (* loaded here as well as by [instantiate_ext_files]: a validator
                config written inline ([Instance]) is not instantiated by the
                loader, so a nested [Filename] can still arrive here *)
             let gcfg =
               match
                 Or_error.(
                   Qualifier.Generator.Config.load_ext_file gcfg
                   >>= ExtFile.unwrap)
               with
               | Ok c -> c
               | Error e -> Error.raise e
             in
             let module G =
               Qualifier.Generator.Make
                 (struct
                   let config = gcfg
                 end)
                 (APCSP)
             in
             fun key args ->
               List.map ~f:snd @@ Set.to_list
               @@ G.generate (Ident.tvar_to_pvar key) args Set.Poly.empty
                    (Map.Poly.empty, ClauseGraph.create ())
                    0
       in
       let defined args =
         if config.houdini_defined_body_atoms <= 0 then []
         else
           Template.PredicateArrays.defined_body_quals
             ~limit:config.houdini_defined_body_atoms
             ~defs:(LogicOld.get_inlined_defs ()) args
       in
       (* the problem's clauses and the input's own assertions: a
          preprocessing step can remove a quantifier the input stated *)
       let sources =
         lazy
           [
             HoudiniCandidates.input_quantified_group ();
             Set.to_list (PCSP.Problem.old_formulas_of APCSP.problem);
           ]
       in
       (* one family at a time, [stop] asked before each *)
       let families key args =
         let open HoudiniCandidates in
         List.map
           [
             ( "frame",
               fun () ->
                 frame_equations ~stop ~limit:config.houdini_frame_equations
                   args );
             ( "membership",
               fun () ->
                 memberships ~stop ~limit:config.houdini_contract_memberships
                   ~defs:(LogicOld.get_inlined_defs ()) args );
             ( "inequality",
               fun () ->
                 inequalities ~stop ~limit:config.houdini_oriented_inequalities
                   args );
             ( "quantified",
               fun () ->
                 if config.houdini_quantified_facts <= 0 then []
                 else
                   quantified_facts ~stop ~limit:config.houdini_quantified_facts
                     ~frame:(houdini_frame_args key args)
                     ~sources:(Lazy.force sources) args );
             ( "inclusion",
                 fun () ->
                   if want then houdini_inclusion_family ~stop args else [] );
             ( "exists-membership",
               fun () ->
                 exists_memberships ~stop
                   ~array_pairs:config.houdini_array_pair_memberships
                   ~limit:config.houdini_exists_memberships args );
             ( "guarded-frame",
               fun () ->
                 guarded_frame_equations ~stop
                   ~limit:config.houdini_guarded_frame_equations args );
             ( "empty-guarded-frame",
               fun () ->
                 empty_guarded_frames ~stop
                   ~limit:config.houdini_empty_guarded_frames args );
             ( "length_sum",
               fun () ->
                 length_sums ~stop ~limit:config.houdini_length_sums args );
             ( "last-element",
               fun () ->
                 last_element_equations ~stop
                   ~limit:config.houdini_last_element_equations args );
             ( "affine_element",
               fun () ->
                 affine_elements ~stop ~limit:config.houdini_affine_elements
                   args );
             ( "prefix-element",
               fun () ->
                 if config.houdini_prefix_elements <= 0 then []
                 else
                   prefix_elements ~stop ~limit:config.houdini_prefix_elements
                     ~consts:
                       (input_int_literals ~n:4)
                     args );
             ( "three_term",
               fun () ->
                 three_term_equations ~stop
                   ~limit:config.houdini_three_term_equations args );
             ( "guarded_order",
               fun () ->
                 guarded_orders ~stop ~limit:config.houdini_guarded_orders args
             );
             ( "rec_fun_app",
               fun () ->
                 Template.PredicateArrays.rec_fun_app_quals
                   ~limit:config.houdini_rec_fun_apps
                   ~fenv:(LogicOld.get_fenv ()) args );
             (* the functions a reconstruction pass added (the solver's
                [reconstruct_rec_functions]), as in the template *)
             ( "reconstructed_fun_app",
               fun () ->
                 let names = Atomic.get PCSP.Problem.reconstructed_functions in
                 if Set.is_empty names then []
                 else
                   Template.PredicateArrays.rec_fun_app_quals
                     ~bool_equalities:true
                     ~limit:(Atomic.get PCSatCommon.RecFunReconstruct.qual_limit)
                     ~fenv:
                       (Map.Poly.filter_keys (LogicOld.get_fenv ())
                          ~f:(Set.mem names))
                     args );
           ]
           ~f:(fun (name, gen) ->
             poll stop;
             (name, Common.PhaseTime.with_phase name gen))
       in
       match
       Map.Poly.mapi senv ~f:(fun ~key ~data ->
           poll stop;
           let args = args_of data in
           let atoms =
             try
               let ex =
                 Common.PhaseTime.with_phase "extracted" (fun () ->
                     extracted key args)
               in
               poll stop;
               let de =
                 Common.PhaseTime.with_phase "defined" (fun () -> defined args)
               in
               let fam = families key args in
               Debug.print
               @@ lazy
                    (sprintf
                       "[houdini] %s over %s: extracted (%d): %s; defined (%d): %s"
                       (Ident.name_of_tvar key)
                       (String.concat_map_list ~sep:"," args ~f:(fst >> Ident.name_of_tvar))
                       (List.length ex)
                       (String.concat_map_list ~sep:" | " ex ~f:Formula.str_of)
                       (List.length de)
                       (String.concat_map_list ~sep:" | " de ~f:Formula.str_of));
               List.iter fam ~f:(fun (name, atoms) ->
                   houdini_print_family key args name atoms);
               (* the generated families are offered as they are: each already
                  holds the orientations that matter (both orders of a
                  pair), and the negation of an equation or of a membership
                  is rarely an invariant, while every candidate costs its
                  questions *)
               ("extracted", HoudiniCandidates.both_polarities ex)
               :: ("defined", HoudiniCandidates.both_polarities de)
               :: fam
             with
             | HoudiniCandidates.Budget_spent as exn_ -> raise exn_
             | exn_ when not (Common.Timer.is_async exn_) ->
               Debug.print
               @@ lazy
                    (sprintf "[houdini] no generated atom for %s: %s"
                       (Ident.name_of_tvar key) (Exn.to_string exn_));
               []
           in
           (args, atoms))
       with
       | m ->
           houdini_generated_cache := Some (want, m);
           Some m
       | exception HoudiniCandidates.Budget_spent ->
           Debug.print
           @@ lazy "[houdini] budget spent while generating candidates";
           None)

  (* the datatypes the problem's own clauses use, which a generated atom must
     agree with; empty (no check) if the clauses themselves do not agree *)
  let houdini_problem_dtenv =
    lazy
      (try
         DTEnv.of_formula @@ Formula.and_of @@ Set.to_list
         @@ PCSP.Problem.old_formulas_of APCSP.problem
       with exn_ when not (Common.Timer.is_async exn_) -> Map.Poly.empty)

  (* the candidate atoms of each unknown: the declared ones, and with
     generation on, the generated ones renamed onto the declared parameters
     (onto [x1 ... xn] when nothing is declared) and merged with them; none at
     all when [stop] ended the generation *)
  (* With COAR_HOUDINI_FAMILY_LOG set in the environment, the pre-pass says
     on stderr, per candidate atom, which generating family offered it and
     how it left the fixed point (or that it stayed), one line each:
       houdini-family: <event> <unknown> <family> pass=<i> clause=<j> rank=<k>
     where <event> is [offered], [model-drop] (a countermodel of a
     conjunction question judged it false; <k> is that countermodel's rank
     among those of the same unknown and clause in the pass, 1 the first),
     [atom-refuted], [atom-undecided], [unasked] (budget spent or clause
     stalled) or [kept].  An instrument: it decides nothing.  The family is
     looked up by the atom's printed form after the renaming onto the
     declared parameters; an atom the merge rewrote is [unknown]. *)
  let houdini_family_log =
    Stdlib.(Sys.getenv_opt "COAR_HOUDINI_FAMILY_LOG" <> None)

  let houdini_family_of : (string, string) Hashtbl.t = Hashtbl.create (module String)

  let houdini_family_key p a = Ident.name_of_tvar p ^ "|" ^ Formula.str_of a

  let houdini_family_event ?(pass = 0) ?(clause = 0) ?(rank = 0) event p a =
    if houdini_family_log then (
      let fam =
        Option.value ~default:"unknown"
          (Hashtbl.find houdini_family_of (houdini_family_key p a))
      in
      Out_channel.output_string stderr
        (sprintf "houdini-family: %s %s %s pass=%d clause=%d rank=%d\n" event
           (Ident.name_of_tvar p) fam pass clause rank);
      Out_channel.flush stderr)

  (* set while the pre-pass runs over the declared atoms alone
     ([houdini_declared_first]) *)
  let houdini_declared_only = ref false

  let houdini_candidates ?(stop = fun () -> false) senv params =
    let generates = houdini_generates () && not !houdini_declared_only in
    match
      if generates then houdini_generated_atoms ~stop
      else Some Map.Poly.empty
    with
    | None -> Map.Poly.empty
    | Some generated_atoms ->
    Map.Poly.filter_mapi senv ~f:(fun ~key ~data ->
        let sorts =
          List.map (Logic.Sort.args_of data) ~f:Logic.ExtTerm.to_old_sort
        in
        let declared = PCSP.Params.candidate_atoms_at params key sorts in
        if not generates then declared
        else
          let args, generated =
            Map.Poly.find_exn generated_atoms key
          in
          let xs, decl =
            match declared with Some e -> e | None -> (args, [])
          in
          let sub =
            Map.Poly.of_alist_exn
            @@ List.map2_exn args xs ~f:(fun (y, _) (x, s) ->
                (y, Term.mk_var x s))
          in
          let generated =
            Common.PhaseTime.with_phase "rename" @@ fun () ->
            List.map generated ~f:(fun (name, atoms) ->
                (name, List.map atoms ~f:(Formula.subst sub)))
          in
          let atoms =
            Common.PhaseTime.with_phase "merge" @@ fun () ->
            let exists_mems, generated' =
              List.partition_tf generated
                ~f:(fst >> String.equal "exists-membership")
            in
            let guarded_frames, generated' =
              List.partition_tf generated'
                ~f:(fst >> String.equal "guarded-frame")
            in
            let empty_guarded, generated' =
              List.partition_tf generated'
                ~f:(fst >> String.equal "empty-guarded-frame")
            in
            let prefix_elems, generated' =
              List.partition_tf generated'
                ~f:(fst >> String.equal "prefix-element")
            in
            let last_elems, generated' =
              List.partition_tf generated'
                ~f:(fst >> String.equal "last-element")
            in
            let own_memberships, generated' =
              if config.houdini_max_membership_candidates > 0 then
                List.partition_tf generated'
                  ~f:(fst >> String.equal "membership")
              else ([], generated')
            in
            (* the inclusion and the affine element families go to their
               own quotas when they have one *)
            let inclusions, others =
              if config.houdini_max_inclusion_candidates > 0 then
                List.partition_tf generated' ~f:(fst >> String.equal "inclusion")
              else ([], generated')
            in
            let affine, others =
              if config.houdini_max_affine_candidates > 0 then
                List.partition_tf others
                  ~f:(fst >> String.equal "affine_element")
              else ([], others)
            in
            let counting, others =
              if config.houdini_max_counting_candidates > 0 then
                List.partition_tf others ~f:(fun (name, _) ->
                    List.mem [ "length_sum"; "three_term"; "guarded_order" ]
                      name ~equal:String.equal)
              else ([], others)
            in
            HoudiniCandidates.merge ~dtenv:(Lazy.force houdini_problem_dtenv)
              ~quota:config.houdini_max_quantified_candidates
              ~inclusion_quota:config.houdini_max_inclusion_candidates
              ~inclusions:(List.concat_map inclusions ~f:snd)
              ~own_quotas:
                [
                  ( List.concat_map exists_mems ~f:snd,
                    config.houdini_exists_memberships );
                  ( List.concat_map guarded_frames ~f:snd,
                    config.houdini_guarded_frame_equations );
                  ( List.concat_map empty_guarded ~f:snd,
                    config.houdini_empty_guarded_frames );
                  ( List.concat_map prefix_elems ~f:snd,
                    config.houdini_prefix_elements );
                  ( List.concat_map last_elems ~f:snd,
                    config.houdini_last_element_equations );
                  ( List.concat_map own_memberships ~f:snd,
                    config.houdini_max_membership_candidates );
                ]
              ~affine_quota:config.houdini_max_affine_candidates
              ~affine:(List.concat_map affine ~f:snd)
              ~counting_quota:config.houdini_max_counting_candidates
              ~counting:(List.concat_map counting ~f:snd)
              ~cap:config.houdini_max_candidates
              ~params:xs ~declared:decl
              ~generated:(List.concat_map others ~f:snd) ()
          in
          if houdini_family_log then (
            List.iter decl ~f:(fun a ->
                Hashtbl.set houdini_family_of ~key:(houdini_family_key key a)
                  ~data:"declared");
            List.iter generated ~f:(fun (name, fatoms) ->
                List.iter fatoms ~f:(fun a ->
                    ignore
                      (Hashtbl.add houdini_family_of
                         ~key:(houdini_family_key key a) ~data:name
                        : [ `Ok | `Duplicate ])));
            List.iter atoms ~f:(fun a -> houdini_family_event "offered" key a));
          (* [houdini_drop_premise_atoms]: a generated atom every clause
             applying the unknown already has as a premise is left out.
             Leaving one in is never wrong (dropping is only a saving), so a
             problem that is not in clausal form, whose clauses cannot be
             read, keeps every atom *)
          let atoms =
            match PCSP.Problem.clauses_of_opt APCSP.problem with
            | Some clauses when config.houdini_drop_premise_atoms ->
              let redundant =
                HoudiniCandidates.premise_redundant (Set.to_list clauses) key xs
              in
              let kept, dropped =
                List.partition_tf atoms ~f:(fun a ->
                    List.mem decl a ~equal:phys_equal || not (redundant a))
              in
              Debug.print
              @@ lazy
                   (sprintf "[houdini] %s: %d atom(s) already premises: %s"
                      (Ident.name_of_tvar key) (List.length dropped)
                      (String.concat_map_list ~sep:" | " dropped
                         ~f:Formula.str_of));
              kept
            | _ -> atoms
          in
          (* the census: for each declared atom, which classes generate it
             too (compared in normal form, an equation either way round) *)
          Debug.print
          @@ lazy
               (let keys =
                  List.map generated ~f:(fun (name, atoms) ->
                      ( name,
                        Set.Poly.of_list
                        @@ List.concat_map atoms
                             ~f:HoudiniCandidates.census_keys ))
                in
                String.concat_map_list ~sep:"\n" decl ~f:(fun d ->
                    let dk = HoudiniCandidates.census_keys d in
                    sprintf "[houdini census] %s: %s <- %s"
                      (Ident.name_of_tvar key) (Formula.str_of d)
                      (match
                         List.filter_map keys ~f:(fun (name, ks) ->
                             if List.exists dk ~f:(Set.mem ks) then Some name
                             else None)
                       with
                      | [] -> "none"
                      | ns -> String.concat ~sep:"," ns)));
          Debug.print
          @@ lazy
               (sprintf "[houdini] %s: %d declared, %d of %d generated kept"
                  (Ident.name_of_tvar key) (List.length decl)
                  (List.length atoms - List.length decl)
                  (List.sum (module Int) generated ~f:(snd >> List.length)));
          if List.is_empty atoms then None else Some (xs, atoms))

  (* how many questions the last pre-pass asked, and whether its budget ran
     out; read by the tests *)
  let houdini_last_questions = ref 0
  let houdini_last_spent = ref false

  (* whether the last fixed point ran inside a pre-pass window
     ([houdini_deadline] set), read by the tests *)
  let houdini_last_windowed = ref false

  (* how many atoms the last pre-pass dropped without asking, after a question
     about the same clause ran out of its budget in the same pass
     ([houdini_skip_clause_after_timeout]); read by the tests *)
  let houdini_last_skipped = ref 0
  (* every question the pre-pass asks, newest first, as (unknown, candidate
     atom); never cleared here, read and cleared by the tests *)
  let houdini_question_log : (Ident.tvar * Formula.t) list ref = ref []

  (* how many rounds the last pre-pass ran; read by the tests *)
  let houdini_last_rounds = ref 0

  (* [f ()] with the pre-pass's deadline set to [houdini_budget_ms] from now
     and restored afterwards, on a raise too; an enclosing call's deadline is
     kept, so the fixed point run by [houdini_outcome] shares its budget *)
  let with_houdini_deadline ?(budget_ms = config.houdini_budget_ms) f =
    match (budget_ms, !houdini_deadline) with
    | None, _ | Some _, Some _ -> f ()
    | Some ms, None ->
        houdini_deadline :=
          Some (Time_ns.add (Common.Clock.now_ns ()) (Time_ns.Span.of_int_ms ms));
        Exn.protect ~f ~finally:(fun () -> houdini_deadline := None)

  (* [budget_ms] is the caller's budget, passed on rather than re-read from
     [houdini_budget_ms]: [with_houdini_deadline] sets no deadline for
     [None], so a fixed point reached through an unbounded caller (the raced
     copy under [houdini_parallel_unbounded]) must not fall back to the
     sequential default here -- doing so cut that copy at 30 s while it
     reported itself unbounded. *)
  let houdini_fixed_point ?(budget_ms = config.houdini_budget_ms) fenv clauses
      : CandSol.t option =
    with_houdini_deadline ~budget_ms @@ fun () ->
    let saved_in_fixed_point = !in_houdini_fixed_point in
    in_houdini_fixed_point := true;
    (fun f ->
      Exn.protect ~f ~finally:(fun () ->
          in_houdini_fixed_point := saved_in_fixed_point))
    @@ fun () ->
    let started = Common.Clock.now_ns () in
    let spent = ref false in
    let out_of_budget () =
      if houdini_budget_spent () then spent := true;
      !spent
    in
    houdini_last_questions := 0;
    houdini_last_spent := false;
    houdini_last_windowed := Option.is_some !houdini_deadline;
    houdini_last_skipped := 0;
    let problem = APCSP.problem in
    let senv = PCSP.Problem.senv_of problem in
    let params = PCSP.Problem.params_of problem in
    let kind_map = PCSP.Problem.kind_map_of problem in
    let ordinary =
      Map.Poly.for_alli senv ~f:(fun ~key ~data:_ ->
          match Map.Poly.find kind_map key with
          | Some Kind.Ord | None -> true
          | Some _ -> false)
    in
    let declared =
      if ordinary then
        Common.PhaseTime.with_phase "gen" (fun () ->
            houdini_candidates ~stop:out_of_budget senv params)
      else Map.Poly.empty
    in
    if out_of_budget () then (
      houdini_last_spent := true;
      Debug.print @@ lazy "[houdini] budget spent before the first question";
      None)
    else if (not ordinary) || Map.Poly.for_all declared ~f:(snd >> List.is_empty)
    then None
    else
      let lam p atoms =
        let xs, _ = Map.Poly.find_exn declared p in
        Logic.Term.mk_lambda (Logic.of_old_sort_env_list xs)
        @@ Logic.ExtTerm.of_old_formula (Formula.and_of atoms)
      in
      let cand_map cur : Logic.cand_map =
        Map.Poly.mapi senv ~f:(fun ~key ~data ->
            match Map.Poly.find cur key with
            | Some atoms -> (data, lam key atoms)
            | None ->
                let xs =
                  List.mapi (Logic.Sort.args_of data) ~f:(fun i s ->
                      (Ident.Tvar (sprintf "x%d" (i + 1)), s))
                in
                (data, Logic.Term.mk_lambda xs (Logic.BoolTerm.mk_bool true)))
      in
      (* whether the last question [valid] asked ran out of its budget, for
         [houdini_skip_clause_after_timeout] *)
      let last_timed_out = ref false in
      (* the countermodel of the last refuted question, for
         [houdini_drop_by_model] *)
      let last_model = ref None in
      (* [houdini_memo_before_simplify]: the decided answers of this fixed
         point by printed unsimplified question *)
      let raw_memo = Hashtbl.create (module String) in
      (* [houdini_simplify_shared_once]: the simplified disjuncts of the
         current clause's shared leaves, by physical identity of the leaf *)
      let leaf_lookup = ref (fun (_ : Formula.t) -> None) in
      let skipped = ref 0 in
      (* [houdini_atom_countermodel_drops]: the judge of the atoms still to be
         asked, set by the per-atom loop for the next question only *)
      let atom_judge_next : (model -> int list) option ref = ref None in
      (* [houdini_shared_body_session]: one solver of a context of this fixed
         point's own, holding the body of one clause at a time; [base_owner]
         names the clause and atom position whose body it holds *)
      let body_session =
        lazy (Z3Smt.Z3interface.base_session_create ~id ())
      in
      let base_owner = ref (-1) and base_owners = ref 0 in
      houdini_skip_weakened_once := false;
      let valid_old phi =
        let raw_key =
          if config.houdini_memo_before_simplify then
            Some
              (Common.PhaseTime.with_phase "raw-key" (fun () ->
                   Formula.str_of phi))
          else None
        in
        match Option.bind raw_key ~f:(Hashtbl.find raw_memo) with
        | Some (`Valid) ->
            last_model := None;
            last_timed_out := false;
            Debug.print @@ lazy "[houdini] question answered as before";
            true
        | Some (`Refuted m) ->
            last_model := m;
            last_timed_out := false;
            Debug.print @@ lazy "[houdini] question answered as before";
            false
        | None ->
        let phi =
          Common.PhaseTime.with_phase "simplify" (fun () ->
              if config.houdini_simplify_shared_once then
                Evaluator.simplify_with_leaf_cache ~lookup:!leaf_lookup phi
              else Evaluator.simplify phi)
        in
        (* With COAR_DUMP_HOUDINI_QUESTIONS=<file> set, every question is
           appended to <file>, one per line, as it is asked, after the
           seconds since the epoch and a tab: an instrument for comparing the
           questions of two runs and the time taken to reach each *)
        (match Sys.getenv "COAR_DUMP_HOUDINI_QUESTIONS" with
        | None | Some "" -> ()
        | Some file ->
            Out_channel.with_file file ~append:true ~f:(fun oc ->
                Out_channel.output_string oc
                  (sprintf "%.3f\t%s\n"
                     (Time_float.to_span_since_epoch (Time_float.now ())
                     |> Time_float.Span.to_sec)
                     (Formula.str_of phi))));
        if Option.is_some SeqInstantiation.instr_file then (
          SeqInstantiation.instr_tag :=
            sprintf "p%d\tc%d\tq-" !houdini_instr_pass !houdini_instr_clause;
          SeqInstantiation.instr_line
            (sprintf "asked\tseq_exists=%b\tsize=%d"
               (binds_sequence_existentially phi) (Formula.ast_size phi)));
        (* each question gets at most what is left of the budget *)
        let timeout = cap_timeout (timeout_for phi) in
        last_model := None;
        houdini_judged_drops := None;
        houdini_pending_judge :=
          Option.map !atom_judge_next ~f:(fun judge -> (phi, judge));
        let res =
          match
            Exn.protect
              ~f:(fun () ->
                Common.PhaseTime.with_phase "check" (fun () ->
                    check_clause_nonparam ~timeout
                      ~verdict_only:config.houdini_fixed_point_verdict_only fenv
                      phi))
              ~finally:(fun () -> houdini_pending_judge := None)
          with
          | `Unsat -> `Valid
          | `Sat model ->
              last_model := Some model;
              `Refuted
          | `Timeout -> `Undecided "timeout"
          | `Unknown r -> `Undecided r
          | exception exn_ when not (Common.Timer.is_async exn_) ->
              `Undecided (Exn.to_string exn_)
        in
        (match res with
        | `Valid -> ()
        | `Refuted -> Debug.print @@ lazy "[houdini] refuted"
        | `Undecided r -> Debug.print @@ lazy ("[houdini] undecided: " ^ r));
        last_timed_out := Stdlib.(res = `Undecided "timeout");
        Option.iter raw_key ~f:(fun key ->
            match res with
            | `Valid -> Hashtbl.set raw_memo ~key ~data:`Valid
            | `Refuted -> Hashtbl.set raw_memo ~key ~data:(`Refuted !last_model)
            | `Undecided _ -> ());
        Stdlib.(res = `Valid)
      in
      let valid uni_senv term =
        valid_old
        @@ Common.PhaseTime.with_phase "build" (fun () ->
               Logic.ExtTerm.to_old_fml Map.Poly.empty uni_senv term)
      in
      let questions = ref 0 in
      (* the clauses with the fewest unknowns in the body first: a fact
         clause refutes most generated atoms, and an atom it drops is not
         asked again in the same pass.  The order changes which questions are
         asked, not the fixed point, which is the largest inductive subset
         whatever the order when every question is decided *)
      let clauses =
        List.stable_sort (Set.to_list clauses)
          ~compare:(fun ((_, _, ns1, _) : Clause.t) (_, _, ns2, _) ->
            Int.compare (Set.length ns1) (Set.length ns2))
      in
      let fam_pass = ref 0 and fam_clause = ref 0 in
      let rec fix cur =
        Int.incr fam_pass;
        fam_clause := 0;
        houdini_instr_pass := !fam_pass;
        let sub =
          Common.PhaseTime.with_phase "pass-setup" (fun () ->
              CandSol.to_subst (CandSol.make (cand_map cur)))
        in
        let subst_linear =
          let f = lazy (Logic.Term.subst_rename_on_capture sub) in
          fun t -> (Lazy.force f) t
        in
        let cur' =
          List.fold clauses ~init:cur
            ~f:(fun cur ((uni_senv, ps, ns, phi) : Clause.t) ->
              (* set once a question about this clause ran out of its budget in
                 this pass ([houdini_skip_clause_after_timeout]) *)
              let stalled = ref false in
              Int.incr fam_clause;
              houdini_instr_clause := !fam_clause;
              Set.fold ps ~init:cur ~f:(fun cur papp ->
                  let p = Logic.Term.pvar_of_atom papp in
                  match Map.Poly.find cur p with
                  | None | Some [] -> cur
                  | Some atoms ->
                      let rest =
                        Set.to_list (Set.remove ps papp)
                        @ List.map (Set.to_list ns) ~f:Logic.BoolTerm.neg_of
                      in
                      (* [phi] and [rest] are the same for every atom asked
                         here, and [sub] is fixed for the pass, so with
                         [houdini_linear_subst] they are substituted once;
                         [Logic.BoolTerm.or_of_parts] then gives each
                         question the disjunction [or_of] would have built,
                         since the substitution sends a constant to itself
                         and distributes over [Or] *)
                      let shared =
                        lazy
                          (List.map (phi :: rest) ~f:(fun t ->
                               (t, subst_linear t)))
                      in
                      (* the shared parts converted once, for
                         [houdini_shared_conversion] *)
                      let shared_old =
                        lazy
                          (List.map (Lazy.force shared) ~f:(fun (t, t') ->
                               ( t,
                                 Logic.ExtTerm.to_old_fml Map.Poly.empty
                                   uni_senv t' )))
                      in
                      if config.houdini_simplify_shared_once then (
                        let leaves =
                          lazy
                            (List.concat_map (Lazy.force shared_old)
                               ~f:(fun (_, part) ->
                                 List.map (Evaluator.disj_leaves [] part)
                                   ~f:(fun leaf ->
                                     ( leaf,
                                       lazy
                                         (Formula.disjuncts_of
                                            (Evaluator.simplify leaf)) ))))
                        in
                        leaf_lookup :=
                          fun leaf ->
                            if not (Lazy.is_val shared_old) then None
                            else
                              List.find_map (Lazy.force leaves)
                                ~f:(fun (l, d) ->
                                  if phys_equal l leaf then Some (Lazy.force d)
                                  else None));
                      let to_old = Logic.ExtTerm.to_old_fml Map.Poly.empty uni_senv in
                      if Option.is_some SeqInstantiation.instr_file then
                        houdini_instr_premise :=
                          Some
                            (lazy
                              (to_old
                                 (subst_linear
                                    (Logic.BoolTerm.or_of (phi :: rest)))));
                      (* [houdini_shared_body_session]: [head]'s question
                         decided against the body held in the fixed point's
                         solver, whose body of this clause and atom position
                         is set there at the first head asked: [`Proved] when
                         the body's other conjuncts and the head's negation
                         are unsatisfiable; [`Refuted] with a model of them
                         that every conjunct set aside holds under
                         ([WeakenedQuery.model_extends]), which is then a
                         countermodel of the whole question; [`Ask]
                         otherwise, when the question is asked as before --
                         and, when the solver found such a model that does
                         not extend, without the weakened question in front
                         of the forked one, which would ask the same thing
                         again *)
                      let owner = (Int.incr base_owners; !base_owners) in
                      let base = ref [] and refused = ref [] in
                      let shared_body_decides head =
                        if
                          (not config.houdini_shared_body_session)
                          || out_of_budget ()
                        then `Ask
                        else
                        Common.PhaseTime.with_phase "shared-body" @@ fun () ->
                        let neg_head =
                          negation_asked (to_old (subst_linear head))
                        in
                        if Z3Smt.Z3interface.may_not_return neg_head then `Ask
                        else
                          let session = Lazy.force body_session in
                          if !base_owner <> owner then (
                            base_owner := owner;
                            Common.PhaseTime.with_phase "set" (fun () ->
                                let body =
                                  Formula.or_of
                                    (List.map (Lazy.force shared_old) ~f:snd)
                                in
                                let r, rest =
                                  List.partition_tf
                                    (Formula.conjuncts_list_of
                                       (negation_asked body))
                                    ~f:Z3Smt.Z3interface.may_not_return
                                in
                                refused := r;
                                base :=
                                  if
                                    (not (List.is_empty rest))
                                    && Z3Smt.Z3interface.base_session_set ~id
                                         session fenv rest
                                  then rest
                                  else []));
                          if List.is_empty !base then `Ask
                          else
                            let timeout =
                              cap_timeout
                                (timeout_for
                                   (Formula.and_of (neg_head :: !base)))
                            in
                            match
                              Common.PhaseTime.with_phase "ask" (fun () ->
                                  Z3Smt.Z3interface.base_session_check ~id
                                    session ~timeout fenv neg_head)
                            with
                            | `Unsat ->
                                Int.incr houdini_shared_body_proofs;
                                Common.PhaseTime.event_here "shared-body-proof";
                                last_model := None;
                                last_timed_out := false;
                                houdini_judged_drops := None;
                                `Proved
                            | `Sat model
                              when Common.PhaseTime.with_phase "extend"
                                     (fun () ->
                                       PCSatCommon.WeakenedQuery.model_extends
                                         ~id
                                         ~ms:(cap_ms
                                                (Option.value timeout
                                                   ~default:10000))
                                         fenv !refused model) ->
                                Int.incr houdini_shared_body_refutations;
                                Common.PhaseTime.event_here
                                  "shared-body-refutation";
                                last_model := Some model;
                                last_timed_out := false;
                                houdini_judged_drops :=
                                  Option.map !atom_judge_next ~f:(fun judge ->
                                      judge model);
                                `Refuted
                            | `Sat _ ->
                                houdini_skip_weakened_once := true;
                                `Ask
                            | `Unknown -> `Ask
                      in
                      let rec ask head =
                        match shared_body_decides head with
                        | `Proved -> true
                        | `Refuted -> false
                        | `Ask ->
                        Exn.protect
                          ~finally:(fun () ->
                            houdini_skip_weakened_once := false)
                          ~f:(fun () ->
                        if
                          config.houdini_linear_subst
                          && config.houdini_shared_conversion
                        then
                          match
                            Common.PhaseTime.with_phase "build" (fun () ->
                                Lazy.force shared_old)
                          with
                          | phi_part :: rest_parts ->
                              valid_old
                              @@ Common.PhaseTime.with_phase "build"
                              @@ fun () ->
                              Logic.BoolTerm.fold_or_of_parts
                                   ~bool:(fun b ->
                                     to_old (Logic.BoolTerm.mk_bool b))
                                   ~or_:(Formula.mk_binop Formula.Or)
                                   (phi_part
                                   :: (head, to_old (subst_linear head))
                                   :: rest_parts)
                          | [] -> assert false
                        else
                          valid uni_senv
                            (Common.PhaseTime.with_phase "build" (fun () ->
                                 question head)))
                      and question head =
                        if config.houdini_linear_subst then
                          match Lazy.force shared with
                          | phi_part :: rest_parts ->
                              Logic.BoolTerm.or_of_parts
                                (phi_part :: (head, subst_linear head)
                               :: rest_parts)
                          | [] -> assert false
                        else
                          Logic.Term.subst sub
                          @@ Logic.BoolTerm.or_of (phi :: head :: rest)
                      in
                      (* [houdini_drop_by_model]: the held atoms asked as one
                         conjunction ([HoudiniByModel.run]) *)
                      let fam_rank = ref 0 in
                      let fam ?rank event a =
                        houdini_family_event ~pass:!fam_pass ~clause:!fam_clause
                          ?rank event p a
                      in
                      let by_model atoms =
                        let instance a =
                          to_old
                          @@ Logic.Term.subst
                               (Map.Poly.singleton p (lam p [ a ]))
                               papp
                        in
                        let held, aside =
                          if config.houdini_drop_by_model_quantified_aside then
                            List.partition_tf atoms ~f:Formula.is_quantifier_free
                          else (atoms, [])
                        in
                        (* [houdini_drop_by_model_batch_ms]: the verdicts
                           one forked copy gave, for the current countermodel,
                           on the atoms the substitution left undecided *)
                        let batch = ref [] in
                        let prejudge model atoms =
                          batch := [];
                          match config.houdini_drop_by_model_batch_ms with
                          | Some ms when not (out_of_budget ()) ->
                              Common.PhaseTime.with_phase "model-batch"
                                (fun () ->
                                  let open_ =
                                    List.filter atoms ~f:(fun a ->
                                        Stdlib.(
                                          HoudiniByModel.judge model (instance a)
                                          = `Undecided))
                                  in
                                  if not (List.is_empty open_) then
                                    let ms = cap_ms ms in
                                    let per = Int.min ms 500 in
                                    match
                                      PCSatCommon.ForkedQuery.run ~ms (fun () ->
                                          List.map open_ ~f:(fun a ->
                                              HoudiniByModel.judge_by_solver
                                                ~sat:(fun phi ->
                                                  match
                                                    Z3Smt.Z3interface.check_sat
                                                      ~id ~timeout:(Some per)
                                                      fenv [ phi ]
                                                  with
                                                  | `Unsat -> `Unsat
                                                  | `Sat _ -> `Sat
                                                  | _ -> `Unknown)
                                                model (instance a)))
                                    with
                                    | Some vs -> batch := List.zip_exn open_ vs
                                    | None -> ())
                          | _ -> ()
                        in
                        HoudiniByModel.run ~aside ~prejudge
                          ~stop:(fun () -> out_of_budget () || !stalled)
                          ~judge:(fun model a ->
                            (fun v ->
                              if Stdlib.(v = `False) then
                                fam ~rank:!fam_rank "model-drop" a;
                              v)
                            @@ Common.PhaseTime.with_phase "model-drop" (fun () ->
                                match config.houdini_drop_by_model_solver_ms with
                                | None -> (
                                    match HoudiniByModel.judge model (instance a) with
                                    | `Undecided -> (
                                        match
                                          List.find !batch ~f:(fun (b, _) ->
                                              phys_equal a b)
                                        with
                                        | Some (_, v) -> v
                                        | None -> `Undecided)
                                    | v -> v)
                                | Some ms ->
                                    HoudiniByModel.judge_by_solver
                                      ~sat:(fun phi ->
                                        if out_of_budget () then `Unknown
                                        else
                                          let ms = cap_ms ms in
                                          match
                                            PCSatCommon.ForkedQuery.run ~ms
                                              (fun () ->
                                                match
                                                  Z3Smt.Z3interface.check_sat
                                                    ~id ~timeout:(Some ms) fenv
                                                    [ phi ]
                                                with
                                                | `Unsat -> `Unsat
                                                | `Sat _ -> `Sat
                                                | _ -> `Unknown)
                                          with
                                          | Some r -> r
                                          | None -> `Unknown)
                                      model (instance a)))
                          ~ask:(fun held ->
                            Int.incr questions;
                            Debug.print
                            @@ lazy
                                 (sprintf "[houdini] %s: conjunction of %d atoms"
                                    (Ident.name_of_tvar p) (List.length held));
                            let head =
                              Common.PhaseTime.with_phase "head" (fun () ->
                                  Logic.Term.subst
                                    (Map.Poly.singleton p (lam p held))
                                    papp)
                            in
                            let proved =
                              in_houdini_conjunction_question := true;
                              Exn.protect
                                ~f:(fun () -> ask head)
                                ~finally:(fun () ->
                                  in_houdini_conjunction_question := false)
                            in
                            if
                              config.houdini_skip_clause_after_timeout
                              && !last_timed_out
                            then stalled := true;
                            if proved then `Proved
                            else
                              match !last_model with
                              | Some model ->
                                  Int.incr fam_rank;
                                  `Refuted model
                              | None -> `Undecided)
                          held
                      in
                      let proved, refuted =
                        if config.houdini_drop_by_model then by_model atoms
                        else ([], [])
                      in
                      (* [houdini_atom_countermodel_drops]: the positions of
                         [atoms] a countermodel of an earlier atom's question
                         in this pass made false, and each atom's ground
                         instance, built once per clause and pass *)
                      let model_dropped = Hash_set.create (module Int) in
                      let instances =
                        lazy
                          (Array.of_list
                             (List.map atoms ~f:(fun a ->
                                  to_old
                                  @@ Logic.Term.subst
                                       (Map.Poly.singleton p (lam p [ a ]))
                                       papp)))
                      in
                      let judge_after i model =
                        let insts = Lazy.force instances in
                        List.filter
                          (List.range (i + 1) (Array.length insts))
                          ~f:(fun j ->
                            (not (Hash_set.mem model_dropped j))
                            && Stdlib.(
                                 HoudiniByModel.judge model insts.(j) = `False))
                      in
                      let kept =
                        List.filteri atoms ~f:(fun i a ->
                            List.mem proved a ~equal:phys_equal
                            || (not (List.mem refuted a ~equal:phys_equal))
                               && (not
                                     (Hash_set.mem model_dropped i
                                     && (fam "atom-model-drop" a;
                                         Int.incr houdini_atom_model_drops;
                                         Common.PhaseTime.event_here
                                           "atom-model-drop";
                                         true)))
                               &&
                            (* a spent budget answers every question left as
                               undecided without asking it, which drops the
                               atom as a question the solver left undecided
                               would *)
                            (let go =
                               (not (out_of_budget ())) && not !stalled
                             in
                             if not go then fam "unasked" a;
                             go)
                            &&
                            (not (out_of_budget ()))
                            && (not
                                  (!stalled
                                  && (Int.incr skipped;
                                      true)))
                            &&
                            (Int.incr questions;
                            houdini_question_log :=
                              (p, a) :: !houdini_question_log;
                            Debug.print
                            @@ lazy
                                 (sprintf "[houdini] %s: %s"
                                    (Ident.name_of_tvar p) (Formula.str_of a));
                            let head =
                              Common.PhaseTime.with_phase "head" (fun () ->
                                  Logic.Term.subst
                                    (Map.Poly.singleton p (lam p [ a ]))
                                    papp)
                            in
                            if config.houdini_atom_countermodel_drops then (
                              ignore (Lazy.force instances : Formula.t array);
                              atom_judge_next := Some (judge_after i));
                            let r =
                              in_houdini_atom_question := true;
                              Exn.protect
                                ~f:(fun () -> ask head)
                                ~finally:(fun () ->
                                  in_houdini_atom_question := false;
                                  atom_judge_next := None)
                            in
                            (* only a refutation's countermodel is read *)
                            (if
                               config.houdini_atom_countermodel_drops
                               && (not r) && Option.is_some !last_model
                             then
                               match !houdini_judged_drops with
                               | Some drops ->
                                   List.iter drops ~f:(Hash_set.add model_dropped);
                                   if not (List.is_empty drops) then
                                     Debug.print
                                     @@ lazy
                                          (sprintf
                                             "[houdini] the countermodel also \
                                              refutes %d atom(s) still to be \
                                              asked"
                                             (List.length drops))
                               | None -> ());
                            houdini_judged_drops := None;
                            if not r then
                              fam
                                (if Option.is_none !last_model then "atom-undecided"
                                 else "atom-refuted")
                                a;
                            if
                              config.houdini_skip_clause_after_timeout
                              && !last_timed_out
                            then stalled := true;
                            r))
                      in
                      Map.Poly.set cur ~key:p ~data:kept))
        in
        if
          Map.Poly.equal (fun a b -> List.length a = List.length b) cur cur'
        then cur
        else fix cur'
      in
      let cur =
        Common.PhaseTime.with_phase "fix" (fun () ->
            fix (Map.Poly.map declared ~f:snd))
      in
      Map.Poly.iteri cur ~f:(fun ~key ~data ->
          List.iter data ~f:(fun a -> houdini_family_event "kept" key a));
      houdini_last_questions := !questions;
      houdini_last_spent := !spent;
      houdini_last_skipped := !skipped;
      if !skipped > 0 then
        Debug.print
        @@ lazy
             (sprintf
                "[houdini] %d atom(s) dropped unasked after a clause's question \
                 ran out of its budget"
                !skipped);
      Debug.print
      @@ lazy
           (String.concat_map_list ~sep:"\n" (Map.Poly.to_alist cur)
              ~f:(fun (p, atoms) ->
                String.concat_map_list ~sep:"\n" atoms ~f:(fun a ->
                    sprintf "[houdini census-kept] %s: %s"
                      (Ident.name_of_tvar p) (Formula.str_of a))));
      Debug.print
      @@ lazy
           (sprintf "[houdini] %d questions in %.1f s; kept %s" !questions
              (Time_ns.Span.to_sec (Time_ns.diff (Common.Clock.now_ns ()) started))
              (String.concat_map_list ~sep:"; " (Map.Poly.to_alist cur)
                 ~f:(fun (p, atoms) ->
                   sprintf "%s: %s" (Ident.name_of_tvar p)
                     (Formula.str_of (Formula.and_of atoms)))));
      if !spent then (
        (* every atom the spent budget left unconfirmed was dropped, so there
           is nothing left to try *)
        Debug.print
        @@ lazy
             (sprintf "[houdini] budget spent after %d questions" !questions);
        None)
      else Some (CandSol.make (cand_map cur))

  (* One round of the pre-pass, and its outcome: [`Solution] when its fixed
     point passes the ordinary check against every clause,
     [`Counterexamples cexs] with exactly that check's counterexamples
     otherwise (never empty), and
     [`Not_applicable] when there is nothing to try (no declared atom, or an
     unknown of another kind than the ordinary one, or a budget that ran
     out).  [record] is given each counterexample's derivation, as an
     ordinary validation counterexample's is, only when the outcome is
     [`Counterexamples].

     With a budget ([budget_ms], which [houdini_outcome] passes as
     [houdini_budget_ms] or, for a second round, the round's own), one
     wall-clock budget covers the whole of this
     function: candidate generation, the fixed point and the final check.  Each
     solver question gets at most what is left of it, a clause the final check
     has not reached when it runs out is not asked, and a question it cut short
     comes back undecided.  When it has run out by the end of the check (to
     within 100 ms), the outcome is [`Not_applicable] -- nothing is
     reported and nothing is learnt, and the loop goes on as it would have
     without the pre-pass; a fixed point every clause was shown to hold for is
     still reported as a solution.  Only the parts outside a solver call
     (building, normalising, substituting and simplifying formulas, and one
     call into the qualifier generator) are not cut short, so the budget can be
     overrun by the longest of those.

     With [houdini_budget_ms], the pre-pass ([houdini_outcome]) is also not
     run at all inside a nested solve bounded by a deadline (the finite instantiation of a
     quantified sort): such a solve reports only a refutation, which the
     pre-pass cannot produce -- its solution would be discarded and its
     counterexamples are what the solve's first validation finds anyway --
     while its questions spend the deadline.  An input the loop refutes in
     2 s inside such a solve lost that answer to a pre-pass that used the
     whole of the solve's 10 s. *)
  (* With [houdini_final_check_retry_ms = Some ms], the final check's
     [retry_undecided]: a clause whose question timed out is asked once more,
     its [negation_asked] in a forked copy killed after [ms] with no solver
     timer, and [`Unsat] (the clause holds) is returned only when the copy
     answered so; every other answer, the copy's refutation included (its
     model does not survive the trip back), returns [res] unchanged.  Counted
     in [houdini_final_retries] (asked, proved), read by the tests. *)
  let houdini_final_retries = (ref 0, ref 0)

  (* With [houdini_final_check_by_pieces], an undecided clause [phi] of the
     final check asked by its pieces: [`Unsat] (the clause holds) when it has
     more than one piece and each piece's question is [`Unsat]; [res]
     unchanged otherwise, at the first piece that is not proved or once the
     pre-pass's budget is spent.  Counted in [houdini_final_pieces] (clauses
     split, clauses proved by their pieces), read by the tests. *)
  let houdini_final_pieces = (ref 0, ref 0)

  (* With [COAR_DUMP_HOUDINI_PIECES=dir] in the environment, each piece the
     final check asks is kept as [dir/qN-PID_native.smt2] (its validity
     question as SMT-LIB, written before it is asked, so that a piece cut
     short by the process's end can still be replayed in a process of its
     own; with [COAR_DUMP_VARIANTS] also its exact rewrites) and
     [dir/qN-PID_k.smt2] (the solver checks it makes), and one line per
     piece answered is appended to [dir/index.tsv].  A diagnostic; nothing is
     written and the answer is unchanged without the variable. *)
  let houdini_piece_dump_count = Atomic.make 0

  let check_piece_dumped ~timeout fenv p =
    Z3Smt.Z3interface.with_validity_dump ~native:false
      ~var:"COAR_DUMP_HOUDINI_PIECES" ~counter:houdini_piece_dump_count ~id
      ~timeout:(Option.value timeout ~default:0)
      ~outcome:(function
        | `Unsat -> "valid" | `Sat _ -> "invalid" | _ -> "undecided")
      fenv p
    @@ fun () ->
    Z3Smt.Z3interface.dump_native_question ~id fenv p;
    check_clause_nonparam ~timeout fenv p

  let houdini_final_by_pieces fenv phi res =
    match res with
    | (`Timeout | `Unknown _) when config.houdini_final_check_by_pieces -> (
        match ClausePieces.of_clause phi with
        | [] | [ _ ] -> res
        | ps ->
            incr (fst houdini_final_pieces);
            let n = List.length ps in
            let rec go k = function
              | [] ->
                  incr (snd houdini_final_pieces);
                  Debug.print
                  @@ lazy
                       (sprintf "[houdini] final check: valid by its %d pieces"
                          n);
                  `Unsat
              | p :: rest -> (
                  if houdini_budget_spent () then res
                  else
                    match check_piece_dumped ~timeout:(timeout_for p) fenv p
                    with
                    | `Unsat -> go (k + 1) rest
                    | _ ->
                        Debug.print
                        @@ lazy
                             (sprintf
                                "[houdini] final check: piece %d of %d not \
                                 proved: %s"
                                k n (Formula.str_of p));
                        res)
            in
            go 1 ps)
    | _ -> res

  let houdini_final_retry fenv phi res =
    let res = houdini_final_by_pieces fenv phi res in
    match (config.houdini_final_check_retry_ms, res) with
    | Some ms, `Timeout -> (
        incr (fst houdini_final_retries);
        let neg_phi = negation_asked phi in
        let started = Common.Clock.now_float () in
        let r =
          PCSatCommon.ForkedQuery.valid_within ~ms (fun () ->
              match
                Z3Smt.Z3interface.check_sat ~id ~timeout:None fenv [ neg_phi ]
              with
              | `Unsat -> `Valid
              | `Sat _ -> `Invalid ()
              | `Timeout -> `Timeout
              | `Unknown r -> `Unknown r)
        in
        Debug.print
        @@ lazy
             (sprintf "[houdini] final check: a timed-out clause asked again: %s in %.3f s (budget %d ms)"
                (match r with
                | `Valid -> "valid"
                | `Timeout -> "killed or timeout"
                | `Unknown r -> "undecided, " ^ r)
                (elapsed_since started) ms);
        match r with
        | `Valid ->
            incr (snd houdini_final_retries);
            `Unsat
        | _ -> res)
    | _ -> res

  let houdini_round ~record ~budget_ms fenv clauses =
    let saved = !in_houdini_seq_instantiation in
    in_houdini_seq_instantiation := config.houdini_seq_instantiation;
    (fun f ->
      Exn.protect ~f ~finally:(fun () -> in_houdini_seq_instantiation := saved))
    @@ fun () ->
    with_houdini_deadline ~budget_ms @@ fun () ->
    match houdini_fixed_point ~budget_ms fenv clauses with
    | None -> `Not_applicable
    | Some cand ->
        let recorded = ref [] in
        let cexs =
          Common.PhaseTime.with_phase "final" @@ fun () ->
          houdini_in_final := true;
          Exn.protect
            ~finally:(fun () -> houdini_in_final := false)
            ~f:(fun () ->
              find_all_counterexamples
                ~record:(fun ex sub -> recorded := (ex, sub) :: !recorded)
                ~stop:houdini_budget_spent
                ~retry_undecided:(houdini_final_retry fenv)
                (if config.houdini_final_check_goals_only then
                   Set.filter clauses ~f:(fun ((_, ps, _, _) : Clause.t) ->
                       Set.is_empty ps)
                 else clauses)
                fenv cand)
        in
        let cut_short = houdini_budget_nearly_spent () in
        if Set.is_empty cexs then (
          Debug.print
          @@ lazy "[houdini] the fixed point satisfies every clause";
          `Solution cand)
        else if cut_short then (
          Debug.print
          @@ lazy
               "[houdini] budget spent in the final check of the fixed point; \
                nothing is reported";
          `Not_applicable)
        else (
          List.iter (List.rev !recorded) ~f:(fun (ex, sub) -> record ex sub);
          Debug.print
          @@ lazy
               (sprintf
                  "[houdini] the fixed point is not a solution (%d \
                   counterexamples); going on"
                  (Set.length cexs));
          `Counterexamples cexs)

  (* One round, or two under [houdini_inclusions_second_round]
     ([HoudiniCandidates.rounds] states which run): round 1 generates no
     inclusion and records no derivation, since its counterexamples are
     dropped whenever they arise (round 2 then runs); each round has its own
     budget, a fresh deadline set by [houdini_round]. *)
  (* [unbounded]: no budget, and yet a pre-pass window.  Whether a question is
     asked inside the pre-pass is read off [houdini_deadline] being set: the
     killed copy for a question that may not return, the memo of decided
     questions, the axiom-first final check's window.  With no deadline at all
     those are silently the outside-the-pre-pass forms, and on a Rust-derived
     [try_fold] the raced copy then asked every quantified question in process
     under a solver timer that does not hold over sequences (one question took
     79 s, the fixed point 165 s).  So an unbounded pre-pass runs under a
     deadline this far away instead -- about eleven days, past any run, and
     within a solver's millisecond budget -- which caps nothing and keeps the
     window. *)
  let houdini_unbounded_window_ms = 1_000_000_000

  let houdini_outcome_once ?(record = fun _ _ -> ()) ?(unbounded = false)
      ?(budget_ms = config.houdini_budget_ms) fenv clauses =
    houdini_last_rounds := 0;
    if Option.is_some budget_ms && PCSatCommon.SolveDeadline.active ()
    then (
      Debug.print
      @@ lazy "[houdini] not run inside a nested solve bounded by a deadline";
      `Not_applicable)
    else
      let budget_ms =
        match budget_ms with
        | None when unbounded -> Some houdini_unbounded_window_ms
        | b -> b
      in
      HoudiniCandidates.rounds ~second_round:houdini_two_rounds
        ~budget_ms
        ~round_budget_ms:config.houdini_inclusion_round_budget_ms
        ~round:(fun ~inclusions ~budget_ms ->
          Int.incr houdini_last_rounds;
          if houdini_two_rounds then
            Debug.print
            @@ lazy
                 (sprintf "[houdini] round %d (%s the inclusions)"
                    !houdini_last_rounds
                    (if inclusions then "with" else "without"));
          houdini_with_inclusions := inclusions;
          Exn.protect
            ~finally:(fun () -> houdini_with_inclusions := true)
            ~f:(fun () ->
              houdini_round
                ~record:
                  (if houdini_two_rounds && not inclusions then fun _ _ -> ()
                   else record)
                ~budget_ms fenv clauses))

  let houdini_outcome ?(record = fun _ _ -> ()) ?(unbounded = false)
      ?(budget_ms = config.houdini_budget_ms) fenv clauses =
    if config.houdini_declared_first && houdini_generates () then
      let first =
        houdini_declared_only := true;
        Exn.protect
          ~finally:(fun () -> houdini_declared_only := false)
          ~f:(fun () ->
            Common.PhaseTime.with_phase "houdini-declared-first" @@ fun () ->
            houdini_outcome_once ~unbounded ~budget_ms fenv clauses)
      in
      match first with
      | `Solution _ as sol ->
          Debug.print
          @@ lazy "[houdini] the declared atoms alone are a solution";
          sol
      | `Counterexamples _ | `Not_applicable ->
          houdini_outcome_once ~record ~unbounded ~budget_ms fenv clauses
    else houdini_outcome_once ~record ~unbounded ~budget_ms fenv clauses

  let houdini_candidate fenv clauses : CandSol.t option =
    match houdini_outcome fenv clauses with
    | `Solution cand -> Some cand
    | `Counterexamples _ | `Not_applicable -> None

  (* the recorder every validation counterexample goes through *)
  let record_in vs ex sub =
    VersionSpace.record_derivation vs ex ~rule:"instance" ~subst:(Some sub)

  (* A counterexample as it enters the example set: normalised, with its
     derivation copied onto the normal form, exactly as the counterexamples
     of a rejected sampled candidate are *)
  let normalize_counterexamples vs cexs =
    let unknowns = Map.key_set @@ PCSP.Problem.senv_of APCSP.problem in
    Set.Poly.map cexs ~f:(fun (ex, srcs) ->
        let ex' = ExClause.normalize_params unknowns @@ ExClause.normalize ex in
        VersionSpace.copy_derivation vs ~from:ex ~to_:ex';
        (ex', srcs))

  (* the pre-pass runs at most once per solve, before the first synthesis or
     inside the first validation *)
  let houdini_done = ref false

  (* Asked by the coordinator once, before the first synthesis.  [None]: the
     loop starts as it would have (the switch is off, the pre-pass has run, the
     state is not a continuing one, there is nothing to try, or the fixed point
     is not a solution and no feedback is asked for).  [Some (Sat sol)]: the
     fixed point is a solution.  [Some (Continue ...)]: the version space with
     the fixed point's counterexamples added as examples, which the phases
     following validation are to process before the first synthesis. *)
  (* What the pre-pass's outcome makes of the version space [vs] before the
     first synthesis: the answer for a solution; with
     [houdini_feedback_counterexamples], [vs] with exactly the outcome's
     counterexamples added (normalised as a validation round's are) and nothing
     else; otherwise [None], leaving [vs] untouched. *)
  let state_of_houdini_outcome vs = function
    | `Solution sol ->
        Debug.print
        @@ lazy "*** a genuine solution is found (houdini, before synthesis): ";
        Debug.print @@ lazy (CandSol.str_of sol);
        Some (State.Sat sol)
    | `Counterexamples cexs when config.houdini_feedback_counterexamples ->
        let examples = normalize_counterexamples vs cexs in
        Debug.print
        @@ lazy
             (sprintf
                "[houdini] %d counterexamples of the fixed point added before \
                 the first synthesis"
                (Set.length examples));
        Some (State.of_examples vs examples)
    | `Counterexamples _ | `Not_applicable -> None

  let run_houdini_prepass (e : State.u) : State.u option =
    if (not config.houdini_before_synthesis) || !houdini_done then None
    else
      match e with
      | State.Continue (vs, ()) -> (
          houdini_done := true;
          let clauses =
            Set.union (PCSP.Problem.clauses_of APCSP.problem)
            @@ Set.Poly.of_list
            @@ Hash_set.to_list vs.learned_clauses
          in
          state_of_houdini_outcome vs
          @@ houdini_outcome ~record:(record_in vs) vs.fenv clauses)
      | _ -> None

  let houdini_in_parallel =
    config.houdini_in_parallel && config.houdini_before_synthesis

  (* Run in the forked copy of [houdini_in_parallel] (the process never calls
     it; it only skips the sequential forms).  Contract: [Some (Sat sol)] for
     a fixed point the ordinary check showed every clause to hold for -- the
     outcome the sequential pre-pass reports as [Sat]; [Some st] with [st] the
     state [state_of_houdini_outcome] makes of a failed fixed point's
     counterexamples, only with [houdini_feedback_counterexamples] and only
     when the outcome came within [houdini_budget_ms] of the pre-pass's start
     (the sequential budget; always, when that is [None]); [None] otherwise.
     So every non-[None] result is a state the sequential pre-pass under
     [houdini_budget_ms] could have returned, or a solution found later, and
     the copy that goes on with it runs what the sequential mode runs.  A
     late failed fixed point gives [None]: taking over then would discard the
     loop's progress for examples the sequential mode would not have had. *)
  let houdini_parallel_prepass (e : State.u) : State.u option =
    if !houdini_done then None
    else (
      houdini_done := true;
      match e with
      | State.Continue (vs, ()) ->
          let clauses =
            Set.union (PCSP.Problem.clauses_of APCSP.problem)
            @@ Set.Poly.of_list
            @@ Hash_set.to_list vs.learned_clauses
          in
          let budget_ms =
            if config.houdini_parallel_unbounded then None
            else
              match config.houdini_parallel_budget_ms with
              | Some _ as b -> b
              | None -> config.houdini_budget_ms
          in
          let started = Common.Clock.now_ns () in
          let outcome =
            houdini_outcome ~record:(record_in vs)
              ~unbounded:config.houdini_parallel_unbounded ~budget_ms vs.fenv
              clauses
          in
          let in_sequential_budget =
            match config.houdini_budget_ms with
            | None -> true
            | Some ms ->
                Time_ns.Span.(
                  Time_ns.diff (Common.Clock.now_ns ()) started <= of_int_ms ms)
          in
          (match outcome with
          | `Counterexamples _ when not in_sequential_budget ->
              Debug.print
              @@ lazy
                   "[houdini] in parallel: the fixed point is not a solution \
                    and came after the sequential budget; nothing fed back"
          | _ -> ());
          (match outcome with
          | `Solution sol ->
              Debug.print
              @@ lazy "*** a genuine solution is found (houdini, in parallel): ";
              Debug.print @@ lazy (CandSol.str_of sol)
          | _ -> ());
          if in_sequential_budget then state_of_houdini_outcome vs outcome
          else (
            match outcome with
            | `Solution sol -> Some (State.Sat sol)
            | `Counterexamples _ | `Not_applicable -> None)
      | _ -> None)

  (* The eager form: before the first round, unless the pre-pass is lazy. *)
  let houdini_before_synthesis (e : State.u) : State.u option =
    if houdini_in_parallel then None
    else
    match config.houdini_after_seconds with
    | Some _ -> None
    | None -> run_houdini_prepass e

  (* The lazy form: at a later round boundary, once [t] seconds have passed.
     [run_houdini_prepass] sets [houdini_done], so it runs at most once, and
     not at all once the pre-pass inside the first validation has run. *)
  let houdini_at_round_boundary ~elapsed_s (e : State.u) : State.u option =
    match config.houdini_after_seconds with
    | Some _ when houdini_in_parallel -> None
    | Some t when Float.(elapsed_s >= of_int t) ->
        Debug.print
        @@ lazy
             (sprintf "[houdini] lazy pre-pass at a round boundary, %.1f s in"
                elapsed_s);
        run_houdini_prepass e
    | _ -> None

  let houdini_seq_instantiation = config.houdini_seq_instantiation

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
    receive_bounds vs;
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
        config.houdini_declared_atoms && (not houdini_in_parallel)
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
                let cexs =
                  find_all_counterexamples
                    ~record:(fun ex sub ->
                      VersionSpace.record_derivation vs ex ~rule:"instance"
                        ~subst:(Some sub))
                    hard_clauses vs.fenv cand
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
        when config.houdini_feedback_counterexamples ->
          First (Set.union examples (normalize_counterexamples vs cexs))
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
      when match config.give_up_after_undecided with
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
