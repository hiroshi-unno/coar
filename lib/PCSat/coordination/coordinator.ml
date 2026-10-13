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

  type t = {
    phase_list : phase list; [@default [ S (Common.Util.ExtFile.Filename "./config/pcsat/synthesizer/tbq_ar.json"); V (Common.Util.ExtFile.Filename "./config/pcsat/validator/nce.json"); L (Common.Util.ExtFile.Filename "./config/pcsat/labeler/sat1.json"); R (Common.Util.ExtFile.Filename "./config/pcsat/resolver/smt.json"); L (Common.Util.ExtFile.Filename "./config/pcsat/labeler/sat1.json") ]]
    rl_config : RLConfig.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/rl/disable.json"]
    verbose : bool; [@default false]
    build_synthesizer_on_first_use : bool; [@default true]
        (** build the synthesis phase when it is first run instead of with the
            other phases before the loop.  The loop's first iteration can ask
            the validator's pre-pass before any synthesis, and with
            [houdini_in_parallel] that pre-pass is raced in a forked copy at
            once; building the synthesizer first delays the copy by the whole
            build (the qualifier and template construction, 4-15 s on an input
            with a few dozen clauses over sequences, most of it outside the
            solver), although the copy needs it only if it hands back
            counterexamples for a later round.  With this on the copy is forked
            before the build, the process builds the synthesizer right after
            the fork, and the copy builds its own only if it runs a synthesis.
            The synthesizer is the same module either way; only when it is
            built, and so the order of fresh-name draws, changes *)
    dedup_normalized_examples : bool; [@default true]
        (** store at most one spelling of an example per its
            [ExClause.normalize] form: an example arriving in another spelling
            of one already held is identified with it
            ([ClauseGraph.spelling_of]).  When off, the example sets are keyed
            on the value as it arrives, and the labeler's normalised copy of an
            unnormalised example is kept beside it *)
    eliminate_tot_preds : bool; [@default false]
        (** also solve away, before the loop, a [Tot u] predicate occurring
            only in clauses [P(t) => phi] (see [eliminate_fn_preds]); when
            off, a [Tot] predicate is always left to the templates *)
    onepoint_split_no_unknown_query : bool; [@default true]
        (** when preprocessing leaves no predicate variable and the
            unrewritten validity questions are undecided, also ask them after
            the one-point rule, the single-constructor split and the
            sequence-length split ([Evaluator.elim_onepoint_and_split_binders],
            all exact), in a fresh solver context; when off, the questions
            asked are exactly the unrewritten ones *)
    no_unknown_query_timeout : int; [@default 10000]
        (** when preprocessing leaves no predicate variable, the wall-clock
            budget in milliseconds of each validity question the zero-unknown
            verdict asks (the conjunction, each clause and piece, the rewritten
            forms, the sequence-instantiated clauses, and the sequence-axiom
            fallback's share).  An undecided question is carried out as
            [timeout] or [unknown], never as a verdict; being wall-clock, the
            same question can be decided on an idle machine and run out on a
            loaded one *)
    no_unknown_refutation_timeout : int; [@default 5000]
        (** the wall-clock budget in milliseconds of each last-resort
            refutation query of the same verdict (pinned array-literal bounds,
            pinned sequence lengths), asked only where the answer would
            otherwise be [timeout] or [unknown] *)
    zero_unknown_reads_strict_deadline : bool; [@default false]
        (** inside a solve bounded by a strict deadline
            ([PCSatCommon.SolveDeadline.within ~strict_budget:true]: the
            true-precondition and lower-bound probes, the nested finite-sort
            solve), the zero-unknown verdict stops once the deadline has passed:
            no further validity question is asked (a question that would have
            been asked is reported as having run out of time) and no further
            stage of its ladder is entered, the verdict being [unknown].  Only
            undecided answers replace questions, so only an answer of the
            bounded solve can be lost, never a wrong one given; outside such a
            solve nothing changes.  [false]: the ladder runs to its end
            whatever the deadline.  Why: the deadline is read only between
            CEGIS phases, and a problem with no unknown left never enters one,
            so a probe given 60 s spent 118-125 s in its ladder and with it the
            whole run of a 120 s budget, three runs of three *)
    no_unknown_query_rlimit : int option; [@default None]
        (** a Z3 resource limit ([rlimit]: a count of the solver's own steps,
            the same whatever the host's load) per query of the zero-unknown
            verdict, beside the wall-clock budgets above, which stay as the
            bound on a query Z3 does not interrupt.  A query that exhausts it is
            treated as one that ran out of time.  [None] sets none *)
    ladder_stage_rlimits_no_unknown_query : (string * int) list; [@default []]
        (** a Z3 resource limit per question for the named stages of the
            zero-unknown verdict's ladder (the stage names its trace prints:
            [quick], [early-seqinst], [conj], ...), in place of
            [no_unknown_query_rlimit] for the questions asked in that stage;
            a stage not named keeps that field's value.  Beside the stage's
            wall-clock budget, which stays as the bound on a check Z3 does not
            interrupt.  Why per stage: a resource count separates the checks
            a stage decides from the ones it cuts only where the stage's
            wall budget is short.  In the 500 ms quick sweep every decided
            check (Z3 5.1.0, Rust-derived inputs) took at most about 12,000
            units and every cut one at least about 69,000; in the 1 s and
            10 s stages the two ranges overlap, because units per second
            differ a hundredfold between questions, so no single count can
            stand in for those budgets.  A count, unlike a wall-clock budget,
            does not move with the host's load.  [[]] sets none *)
    report_budget_exhaustion : bool; [@default false]
        (** when the zero-unknown verdict is left undecided and at least one
            of its validity questions ran out of its budget, answer [unknown]
            rather than [timeout] and say on stderr which budget ran out and
            how many questions it cut ("budget exhausted: ...").  Without it
            such a run answers [timeout], the word the run-wide time limit also
            prints, and the budget's part is visible only in the verbose
            trace *)
    quick_sweep_no_unknown_query : (int * int) option; [@default Some (500, 5000)]
        (** when preprocessing leaves no predicate variable, first ask every
            residual clause -- split into its [ClausePieces] when
            [split_clause_heads_no_unknown_query] is on -- with a short budget
            per question, [(per question, whole sweep)] in milliseconds, before
            the conjunction and the long per-clause questions: a piece shown
            invalid refutes the problem at once, and a clause all of whose
            pieces are shown valid is recorded as valid and not asked again.
            The questions are the ones asked later anyway, so this changes only
            their order and budget.  What it buys: a Thrust problem whose last
            residual clause has a piece refuted in 0.03 s spent 57 s first on
            the conjunction, a rewritten conjunction and a piece of an earlier
            clause, each at the 10 s budget, and on proving two other clauses
            valid.  The sweep stops asking once its whole budget is spent.
            [None] skips it. *)
    quick_sweep_finish_clause_no_unknown_query : bool; [@default true]
        (** with [quick_sweep_no_unknown_query], let the sweep's whole budget
            stop it only between clauses, or inside a clause once one of its
            pieces was left undecided: a clause started before the budget ran
            out is asked to its end while every piece so far was shown valid,
            so that it can still be recorded as valid
            ([NoUnknownLadder.quick_sweep]).  Without it the budget cuts a
            clause at any piece and the pieces already shown valid are lost.
            Only adds questions the sweep would ask of the same pieces, so it
            changes when an answer is reached, never which.  What it buys: a
            tuple variable split into its fields gave a residual clause 60
            pieces (36 unsplit), six of them about 1 s each, and the 5 s sweep
            stopped a few pieces short; the later stages took 40 s more to prove
            the clause, and the file went from 32-59 s to 78-104 s; with this
            on it answered in 30-31 s.  On by default *)
    instantiate_sequence_premises_no_unknown_query : bool; [@default true]
        (** when preprocessing leaves no predicate variable and every validity
            question asked before ends undecided, also ask each clause not yet
            shown valid after instantiating its sequence binders, and then its
            integer binders, where that only strengthens the question
            ([NoUnknownSeqInst]); it can only
            turn [unknown]/[timeout] into [sat], never into [unsat].  On by
            default: it is asked only after every other question ended
            undecided, and on the Thrust corpus it answers the same two
            iterator-extension queries as the sequence-axiom fallback.  When
            off, nothing is asked beyond the existing questions *)
    seq_axioms_first_no_unknown_query : int option; [@default Some 1000]
        (** before each validity question of the zero-unknown verdict that
            mentions a sequence, first ask it with the sequences axiomatised
            (the sequence-axiom encoding), under this budget in milliseconds,
            and read only a proof; the native question follows otherwise.  The
            native sequence theory was measured spending 98% of a Thrust run in
            such questions, while the axiomatised form decides the pointwise
            shape at once.  On by default at 1000 ms: over 205 Thrust and
            quantified-invariant inputs it lost no answer and cut the time of
            the answered ones by about 5%. *)
    seq_axioms_first_fresh_no_unknown_query : bool; [@default false]
        (** apply [seq_axioms_first_no_unknown_query] also to the questions
            asked in a fresh context, which otherwise ask the native sequence
            theory first and reach the axiomatised form only through the
            sequence-axiom fallback, after the native question has spent its
            budget.  Contract: when on (and [seq_axioms_first_no_unknown_query]
            is [Some]), every validity question the ladder asks in a fresh
            context -- the rewritten clauses early and late, the
            sequence-instantiated forms in both passes of the two-pass budget,
            and the point pin's proofs, which all go through one asker -- that
            mentions a sequence is first asked with the sequences axiomatised
            under that budget; when off, those questions are asked exactly as
            before.  The satisfiability questions of the pins, which read a
            model, are not affected: the axiomatised form yields no model.
            Only a proof is read from the axiomatised question, so it can
            only answer [Valid], and that proof is the one the fallback would
            read from the same encoding afterwards; any other outcome hands
            the question to the native theory as before, so a refutation of
            an exact rewrite is still reached, at most one axioms budget
            later.  The switch therefore changes timing only -- which answer
            is reached within the time, never which answer is right.  What it buys: pieces whose native question runs out its
            10 s and whose axiomatised form is proved in under a second, each
            asked 10 s sooner; what it costs: up to the axioms-first budget per
            question the encoding does not prove. *)
    word_instances_first_no_unknown_query : bool; [@default true]
        (** in the early rewritten pass ([exact_forms_first_no_unknown_query]),
            ask each piece (and each whole clause asked) first through the
            words of its matched-instance forms: every quantifier-free form of
            [SeqInstantiation.matched_forms] (every positive existential, a
            premise universal among them, replaced by its instances at the
            piece's own ground terms), and of the same matching in two rounds
            (the second against the ground terms the first round's instances
            write), that converts an integer to a word, asked by
            [Z3interface.check_valid_by_words]; then the piece as it is.  Each
            form implies its piece and the words question is weaker than its
            form, so only a proof is read and only the order of the questions
            changes.  What it buys: a bit set's word and bit obligations, whose
            proof needs a premise at the goal's index and a premise at that
            index's word ([i div 64]) and then only bit-vector reasoning, are
            proved in a fraction of a second, where the piece as it is, and its
            matched forms asked as they are, run out their budget (Z3 does not
            combine [i div 64], [i mod 64] and bits read through [int_to_bv]);
            what it costs: the words questions of a piece they do not prove,
            each answered (a model of the weaker question, which says nothing)
            in about a second.  On by default; best with
            [contextual_ite_no_unknown_query], which removes the
            negative-index branches of a truncated division before the forms
            are matched *)
    word_instances_two_rounds_first_no_unknown_query : bool;
        [@default true]
        (** with [word_instances_first_no_unknown_query], ask each piece's
            two-round matched-instance form through its words first, and its
            one-round form only when the two-round one is past the size bound
            ([SeqInstantiation.word_forms]).  The one-round form implies the
            two-round one (the second pass only adds instances beside those of
            the first), so it is valid only if the two-round form is: dropping
            it costs only a proof the solver would find through the smaller
            form's words and not the larger one's.  Only proofs are read, so
            the answer can only be reached at another time, never be another.
            Why: on a bit-set input the one-round words question of a piece
            ran out of its 10 s where the two-round one was proved in 0.6 s,
            and of another piece both ran out and the piece as it is was
            proved in 2.7 s, so each such piece paid 10 s for a question the
            one after it subsumes.  On by default. *)
    implied_factor_equalities_no_unknown_query : bool; [@default false]
        (** each native question of the zero-unknown verdict (the quick sweep's
            and the fresh-context ones) is asked with the equations between
            the factors of its products that its linear facts imply stated as
            disjuncts [t != u] ([Z3interface.implied_factor_equalities], each
            equation shown by an [unsat] under the question's budget): an
            equivalence in every model, so every answer is one about the
            question.  Why: Z3's nonlinear arithmetic does not compare two
            products [n * t] and [w * i] once the linear part forces [n = w];
            on a bit-set obligation the question ran past 30 s under two of
            three seeds, and in the verdict two fresh 10 s questions of its
            pieces ran 30-88 s, while with [n = w] stated it was answered in
            under 0.12 s under every seed.  Off by default *)
    exact_forms_first_no_unknown_query : bool; [@default true]
        (** after the quick sweep, ask each clause not yet shown valid in its
            rewritten form ([onepoint_split_no_unknown_query]) piece by piece,
            and then the sequence instantiation
            ([instantiate_sequence_premises_no_unknown_query]), BEFORE the long
            questions on the unrewritten conjunction and clauses, instead of
            after them.  Only the order changes: each of these questions can
            refute only through an exact rewrite and prove only validity, so an
            answer is the same whichever order reaches it; what changes is the
            time spent first on questions that run out their budget.  On by default
            together with the next field: over 349 Thrust, quantified-invariant
            and CHC inputs at 120 s the pair answered 296.8 expected against
            294.6 without, with no verdict disagreement. *)
    two_pass_budget_no_unknown_query : int option; [@default None]
        (** [Some ms]: the early rewritten pieces
            ([exact_forms_first_no_unknown_query]) and every form of a piece
            the sequence instantiation asks are first asked with a budget of
            [ms] milliseconds each; only for a piece none of whose forms is
            proved so are the forms that ran out of that budget (not those
            answered invalid or refused for their shape) asked again with
            [no_unknown_query_timeout].  The early rewritten pieces get their
            full-budget question from the later rewritten pass of the ladder,
            which asks them anyway when nothing earlier decides.  Only [`Valid]
            is read from the sequence-instantiated forms and a refutation only
            from an exact rewrite, so this changes when an answer is reached,
            never which: a form that needs more than [ms] is still asked with
            the full budget.  What it buys: a form asked later that is proved
            at once is no longer queued behind an earlier form that spends the
            whole budget -- one Thrust input spent 41 of 46 s in four such
            questions while every decided question of eight profiled inputs
            returned within 2.3 s.  [None]: every question has the full budget
            and the forms are asked once, in order *)
    split_constructor_equations_no_unknown_query : bool; [@default true]
        (** inside the rewrite [onepoint_split_no_unknown_query] switches on,
            also split an equation between two applications of one datatype
            constructor into the equations of their fields (a disequation into
            the disjunction of the fields' disequations), exact by the
            injectivity of constructors; so a bound tuple the single-constructor
            split opened and an equation fixes to a literal is eliminated by
            the one-point rule, and a bound sequence whose length it fixed is
            written out as units *)
    drop_valid_premises_before_pin_no_unknown_query : bool; [@default true]
        (** in the point pin of the zero-unknown verdict, accept a point
            also when the quantified conjuncts of its pinned negation that
            are not proved valid have a model: the conjuncts proved valid
            hold in every model, so dropping them leaves the negation's
            models unchanged, and a model of the rest is a countermodel.
            Only a model is read from the added question.  On by default *)
    seq_array_view_candidates_no_unknown_query : bool; [@default true]
        (** in the sequence instantiation of the zero-unknown verdict, also
            instantiate a positive existential over an array of sort
            [Int -> E] at the array views [lambda k. seq.nth s k] of the
            clause's ground sequences [s] of sort [Seq E]: a loop history a
            clause states once as a premise sequence and once as a goal array
            of the same states is witnessed by the sequence read as an array.
            Sound for validity only, as every instance of a positive
            existential is.  On by default *)
    pointwise_array_witnesses_no_unknown_query : bool; [@default true]
        (** in the sequence instantiation of the zero-unknown verdict, also
            instantiate a positive existential over an array of sort
            [Int -> E] at its pointwise definitions: for an equation
            [select x j = u] in its body, [j] an integer variable and [u]
            mentioning only [j] and the formula's free variables, the array
            [lambda j'. u[j'/j]].  A history stated in the array-and-length
            encoding of sequences, [forall k. 0 <= k < n => ta[k] = k + c], is
            witnessed by that function.  Sound for validity only, as every
            instance of a positive existential is.  On by default *)
    pointwise_array_countermodels_no_unknown_query : bool; [@default false]
        (** in the zero-unknown verdict, when a clause's (or a piece's)
            validity question is left undecided, ask once more, under the
            same budget, the instance of it with each free array of sort
            [Int -> E] replaced by a pointwise definition read off the clause
            ([SeqInstantiation.pointwise_array_instance]), reading only a
            refutation.  Sound for refutation only: the clause holds for every
            value of its free variables, so a countermodel of an instance is
            one of the clause.  Off by default *)
    pin_scalars_binder_free_relaxation_no_unknown_query : bool;
        [@default true]
        (** in the point pin, guess a point first from a quantifier-free
            relaxation of the piece's negation built by taking its binders
            apart from the outside in ([ScalarPin.binder_free_relaxation]):
            an existential's variables made free, a universal over an integer
            replaced by its instances at the integer literals of the formula
            and their negations, any other universal by one instance at a
            fresh variable.  Every model of the negation extends to a model
            of it, so its models cover the countermodels; a point is still
            reported only once the pinned negation is proved.  On by
            default *)
    instantiate_element_binders_no_unknown_query : bool; [@default false]
        (** in the sequence instantiation of the zero-unknown verdict, also
            instantiate an existential over an element of a sort variable or
            an uninterpreted sort, at the indices of the reads of the same
            array outside it, instead of replacing it by [false].  A trait
            law over a quantified sort -- the transitivity of [produces] --
            reaches a clause as such an existential, whose witnesses are the
            states the clause already reads.  Sound for the same reason as the
            other instances: each implies the existential. *)
    split_seq_prefix_over_concat_no_unknown_query : bool; [@default true]
        (** in the sequence instantiation of the zero-unknown verdict, where
            every read of a concatenation is split by index, also split every
            prefix of a concatenation: [extract (a ++ b) 0 k] becomes
            [if k <= len a then extract a 0 k else a ++ extract b 0 (k - len
            a)], and likewise in the clauses asked before any rewriting.  An
            equivalence in every model (SMT-LIB's extraction is empty for
            [k <= 0] and the whole sequence past its end), so the question
            stays the same one. *)
    split_seq_prefix_focus_only_no_unknown_query : bool; [@default true]
        (** with [split_seq_prefix_over_concat_no_unknown_query], split
            prefixes of concatenations only inside the chain-focused and
            associativity-matched forms (their instantiated variant), not in
            the clauses asked before rewriting nor in the deep forms.  Those
            forms hold a few kilobytes and one witness, so the split's
            [ite]s stay few, where applied to a deep form it was measured to
            triple its size; the split is exact wherever it applies, so this
            only chooses which questions carry it *)
    offset_int_candidates_no_unknown_query : bool; [@default true]
        (** in the sequence instantiation of the zero-unknown verdict, also
            offer an integer existential used as a read index or an
            extraction bound the positions [t - len u] and [t + len u], [t] an
            index or extraction bound the clause reads and [u] a sequence
            whose length it mentions, after every other candidate and at most
            eight of them: the position a lemma over prefixes of [u ++ w]
            needs to reach a read of the concatenation at [t].  Sound as the
            other instances are: each implies the existential. *)
    array_read_int_candidates_no_unknown_query : bool; [@default false]
        (** in the sequence instantiation of the zero-unknown verdict, also
            offer an integer existential read as an array index, [a[x + d]],
            the indices [u - d] of the reads [a[u]] of the same array outside
            every binder ([SeqInstantiation.array_read_int_candidates]): the
            witness of a goal [exists j. f[j] = i] over an index map joined
            from two, which is a premise's witness [k] or [k + n] and is read
            by no sequence.  Sound as every instance is: each implies the
            existential.  Off by default: built for one input, not measured
            on a corpus *)
    bool_binder_candidates_no_unknown_query : bool; [@default false]
        (** an existential of the zero-unknown verdict's integer
            instantiation that also binds a [Bool] is instantiated with the
            [Bool] at both values rather than replaced by [false]
            ([SeqInstantiation.bool_binder_candidates]): a law over a
            closure's postcondition, which quantifies over its result.  Sound
            as every instance is.  Off by default: built for one input, not
            measured on a corpus *)
    element_candidates_through_constructors_no_unknown_query : bool;
        [@default false]
        (** with [instantiate_element_binders_no_unknown_query], an element
            binder that is a constructor's argument at an array index,
            [r[c(.., x, ..)]], is also offered the argument at that place of
            the same constructor at that index of a read of [r] outside the
            quantifier
            ([SeqInstantiation.element_candidates_through_constructors]): a
            law over a closure's states [mut c d].  Sound as every instance
            is.  Off by default: built for one input, not measured on a
            corpus *)
    nested_focus_forms_no_unknown_query : bool; [@default false]
        (** the chain-focused and associativity-matched forms of the
            zero-unknown verdict instantiate their integer binders in two
            nested rounds with equated candidates, as the deep forms do
            ([SeqInstantiation.nested_focus_forms]), so that an existential
            exposed by the first round's instances is instantiated rather
            than dropped.  Sound as every instance is.  Off by default: built
            for one input, not measured on a corpus *)
    literal_range_int_candidates_no_unknown_query : bool; [@default false]
        (** in the sequence instantiation of the zero-unknown verdict, also
            offer an integer existential the integers in [-8, 8] satisfying
            every top-level conjunct of its body that mentions it alone, when
            there are at most four
            ([SeqInstantiation.literal_range_int_candidates]): a position of a
            sequence of literal length, such as the one item a filter's step
            visits.  Sound as every instance is.  Off by default: built for
            one input, not measured on a corpus *)
    index_map_shift_candidates_no_unknown_query : bool; [@default false]
        (** with [instantiate_element_binders_no_unknown_query], also offer
            an existential over an array [Int -> Int] the shifts [lambda k. k
            + len u] by the lengths the clause mentions outside every binder,
            and the identity ([SeqInstantiation.index_map_shift_candidates]):
            the index map of a visited suffix [v] of [u ++ v], which a
            filter's [produces] needs after it has produced one item.  Sound
            as every instance is.  Off by default: built for one input, not
            measured on a corpus *)
    index_map_join_candidates_no_unknown_query : bool; [@default false]
        (** with [instantiate_element_binders_no_unknown_query], also offer
            an existential over an array [Int -> Int] the joins [lambda k.
            ite (k < c) g[k] (h[k - c] + d)] of two free index maps at the
            prefix lengths of two concatenations its body mentions
            ([SeqInstantiation.index_map_join_candidates]): the index map of
            [ab ++ bc] over [s1 ++ s2] that a filter's [produces_trans]
            needs, which the input writes as a [lambda] that is beta-reduced
            before instantiation.  Sound as every instance is.  Off by
            default: built for one input, not measured on a corpus *)
    offset_int_candidates_chain_only_no_unknown_query : bool;
        [@default true]
        (** with [offset_int_candidates_no_unknown_query], offer the positions
            [t - len u] and [t + len u] only for a [u] that is an operand of
            the middle argument of a chained pair of ground applications
            [h(s, u1, m)], [h(m, u2, e)] of the piece -- the operands a
            transitivity witness [u1 ++ u2] is built from, and the only [u]
            whose offset a prefix lemma over that witness needs.  Fewer
            instances of the same kind, so sound as they are; with the
            unrestricted rule the extra instances were measured to cost more
            time than they save *)
    onepoint_array_reads_no_unknown_query : bool; [@default true]
        (** inside the rewrite [onepoint_split_no_unknown_query] switches on,
            also eliminate a literal fixing a read of a bound array:
            [exists s. L(s) /\ select s k = t] becomes
            [exists s. L(store s k t)], and a range of reads fixed pointwise:
            [exists s. L(s) /\ forall i. R(i) \/ s[i + c] = u(i)] becomes
            [exists s. L(lam j. ite (not R(j - c)) u(j - c) s[j])] (both
            dually under a universal), exact under array extensionality.  A
            disjunct [exists s. not P(s) /\ x = s[0]] -- the array encoding of
            a sequence witness whose first element an equation fixes -- needs
            a witness array the question does not contain, and Z3 answers
            "incomplete quantifiers" until the store is spelled out; a
            trait law's prepend witness is stated by both shapes at once.
            When off, bound arrays are left as they are *)
    surjective_pairing_no_unknown_query : bool; [@default true]
        (** inside the rewrite [onepoint_split_no_unknown_query] switches on,
            also split an equation [u = C(a1..an)] of a datatype or tuple with
            a single constructor [C] into [sel_1 u = a1 /\ .. /\ sel_n u = an]
            (a disequation into the disjunction of the fields'), when some
            [ai] is a variable of the enclosing quantifier block not occurring
            in [u]; the one-point rule then eliminates it as [sel_i u].  Exact
            by surjective pairing and injectivity; a bound pair of integers a
            projection fixes, [exists v1 v2. t.0 = tuple(v1, v2) /\ ...],
            otherwise stays bound because the projection is no constructor
            application.  On by default: exact, and over 203 sequence and array inputs
            it answered, together with the chain and prepend witness forms, 171.6
            expected against 169.2 without. *)
    surjective_pairing_nested_no_unknown_query : bool; [@default true]
        (** with [surjective_pairing_no_unknown_query], also split such an
            equation when an [ai] mentions a variable of the enclosing block
            not occurring in [u] without being one ([u = TM (mut c d)], two
            single-constructor types, becomes [sel (sel u) = c /\ ..] in two
            steps and [c] is removed).  Exact; only when the split fires
            changes *)
    lift_spine_blocks_no_unknown_query : bool; [@default true]
        (** inside the rewrite [onepoint_split_no_unknown_query] switches on,
            merge a block of the same quantifier that is a conjunct of an
            existential's body (a disjunct of a universal's) into the
            enclosing block, when none of its variables is bound there or
            free in the other parts: [exists xs. A /\ exists ys. B] is
            [exists xs ys. A /\ B].  Exact; what it buys is that an outer
            witness defined only through an inner binder ([w = t ++ s]) is
            removed by the one-point rule *)
    contextual_ite_no_unknown_query : bool; [@default true]
        (** inside the rewrite [onepoint_split_no_unknown_query] switches on,
            also replace an [ite] by the branch its context selects: where a
            sibling conjunct, the negation of a sibling disjunct or an
            enclosing [ite] guard entails the guard (or its negation), decided
            syntactically over integer linear literals.  Exact in every model,
            so it can neither lose nor invent an answer; what it buys is a
            bound array the array-read one-point rule left only in the else
            branch of the lambda it wrote, [k < 0 \/ k >= n \/ ite (0 <= k < n)
            u s[k]], which then no longer occurs and is dropped with its
            binder *)
    contextual_ite_as_extra_form_no_unknown_query : bool; [@default true]
        (** with [contextual_ite_no_unknown_query], apply the contextual
            [ite] rule not in place, to every rewritten clause and every form
            the verdict asks, but only to forms asked in addition, after the
            forms asked without it have failed: each rewritten clause not
            decided piece by piece is asked once more, piece by piece, in its
            contextual-ite form ([Evaluator.elim_onepoint_and_split_binders_contextual]),
            and in the sequence instantiation each piece gets its
            [SeqInstantiation.contextual_ite_form] as its last form, after
            the grouped question of its group and every other form of its own.
            Every other question is then the one asked with
            [contextual_ite_no_unknown_query] off, so the contract is: with
            the field on, every clause and every piece proved, and every
            clause refuted, without the rewrite is proved (resp. refuted) by
            the same question, before any added question is asked.  The added
            questions are exact (the rewrite holds in every model) or
            strengthenings (the instantiation), so a proof read from one is
            sound, and a refutation is read only from the exact clause form.
            Why: applied in place, the rewrite changed the forms the grouped
            piece questions are built from, and on a Rust-derived call-site
            input those questions proved 8 pieces where without it they
            proved 21, turning an input answered 6 of 6 into 1 of 6.  Inert
            without [contextual_ite_no_unknown_query].  On by default. *)
    witness_forms_no_unknown_query : bool; [@default true]
        (** in the sequence instantiation of the zero-unknown verdict, also
            ask each piece, after every other form, in a form shaped for the
            solver's e-matching ([SeqInstantiation.witness_form]): an
            existential's variable that occurs only inside array lambdas
            instantiated at a fresh free variable, and an integer one read
            through [n - c] in a constructor argument or array index renamed
            so it reads as a variable.  A strengthening, so only a proof of
            validity is read from it and it can only turn an undecided piece
            into a proved one.  With [onepoint_array_reads_no_unknown_query],
            a law witness stated pointwise (an array prepending one element
            to another) becomes a lambda the solver instantiates the law
            with *)
    drop_array_hypotheses_no_unknown_query : bool; [@default false]
        (** in the sequence instantiation of the zero-unknown verdict, also
            ask each piece, after every other form (the witness form
            included), with the disjuncts of its negation normal form that
            are existentials binding an array or sequence around a universal
            quantifier removed ([SeqInstantiation.drop_array_hypotheses_form]):
            the negated form of a premise quantified over arrays, which the
            solver's instantiation cannot decide even where the piece does
            not depend on it.  Removing a disjunct strengthens the question,
            so only a proof of validity is read from it and it can only turn
            an undecided piece into a proved one *)
    skolemize_positive_universals_no_unknown_query : bool; [@default true]
        (** in the sequence instantiation of the zero-unknown verdict, first
            replace every universal of a piece reached through conjunctions,
            disjunctions and other such universals alone -- a conclusion's
            universal, or a premise's existential after negation normal form
            -- by fresh free variables, so that terms built from its variables
            become candidate witnesses for a sequence existential beneath it
            and candidate instances of a premise law.  Validity is unchanged
            by that step, so the instantiation's contract is too: only a
            proof of validity is read.  Off by default *)
    cancel_forced_sequence_binders_no_unknown_query : bool; [@default true]
        (** in the sequence instantiation of the zero-unknown verdict, first
            eliminate a sequence binder [x] of an existential whose body has a
            conjunct [p ++ x = q] (or [x ++ p = q]) when the piece has a
            disjunct [p ++ u != q] (respectively [u ++ p != q]) over variables
            not bound there: the existential is replaced by its instance at
            [u].  Exact, by cancellation of a common prefix or suffix: where
            the disjunct is false [x] is forced to be [u], where it is true
            the piece holds.  So the binder is never offered candidates.  On
            by default *)
    subst_projection_definitions_no_unknown_query : bool; [@default false]
        (** before the zero-unknown verdict asks a clause, replace a
            sequence-valued projection of a clause variable, [sel x], by the
            constructor term [t] a disjunct [sel x != t] of the clause defines
            it as, in the clause's other disjuncts
            ([Evaluator.subst_seq_projection_definitions]).  The disjunct is
            kept, so the clause is equivalent to its rewritten form in every
            model.  Off by default *)
    chain_concat_candidates_no_unknown_query : bool; [@default true]
        (** in the sequence instantiation of the zero-unknown verdict, also
            offer a positive sequence existential whose body applies a
            relation [h] (an array read as a chain of [select]s) with the
            binder at position [j] the concatenation [x0 ++ x1] of two
            applications [h(s, x0, m)] and [h(m, x1, e)] of the piece whose
            middle arguments agree -- the witness a transitivity law
            [h(a, u, b) /\ h(b, v, c) => h(a, u ++ v, c)] gives, which the
            clause never writes.  First among the candidates, those whose
            endpoints are the goal's own ahead, at most four.  Sound as the
            other instances are: each implies the existential.  On by
            default *)
    chain_candidates_free_only_no_unknown_query : bool; [@default true]
        (** with [chain_concat_candidates_no_unknown_query], read the chained
            applications only where their arguments mention no variable the
            clause binds, after rebinding such a variable by constructor
            injectivity against an equation over free terms
            ([SeqInstantiation.chain_apps_free_only]), so that the premise
            [forall i. r = Some i => h(b, [i], c)] beside [r = Some x] gives
            the witness [t ++ [x]] rather than [t ++ [i]] with [i] free.  Any
            term is a sound instance, so this changes which forms are built,
            never what a proof means.  When off, the candidates are exactly
            those built without it. *)
    matched_instance_forms_no_unknown_query : bool; [@default true]
        (** in the sequence instantiation of the zero-unknown verdict, ask
            each piece FIRST with every positive existential replaced by its
            instances at the substitutions one round of first-order matching
            of its body's subterms against the piece's ground terms finds
            (at most eight each), [false] where none is found
            ([SeqInstantiation.matched_instance_form]).  Sound for validity
            only: each instance implies its existential, so the form implies
            the piece.  On by default *)
    matched_instance_hyp_budget_no_unknown_query : int option; [@default None]
        (** with [matched_instance_forms_no_unknown_query], the number of
            instances one pass of the earlier-pieces form may make
            ([SeqInstantiation.earlier_pieces_form]; 64 when [None], as for
            the other matched forms).  Only which instances are offered
            changes, so soundness is as above.  [None] by default *)
    matched_instance_element_candidates_no_unknown_query : bool;
        [@default true]
        (** with [matched_instance_forms_no_unknown_query], a sequence binder
            of a positive existential is also offered the one-element
            sequence [seq.unit t] for each element equation [seq.nth x i = t]
            of its body, and [u ++ seq.unit t] for each sequence [u] of its
            sort free in the piece
            ([SeqInstantiation.element_equation_candidates_for]), these only
            where the matches leave room; and [a ++ b] where the body states
            the binder pointwise as [a] below [len a] and [b] above
            ([SeqInstantiation.pointwise_definition_candidates_for]): the
            witness of an existential introduction built from the element the
            goal fixes, or a lemma's concatenation, which the piece never
            writes.  Only which instances are offered changes, so soundness
            is as above.  On by default *)
    matched_instance_chain_join_candidates_no_unknown_query : bool;
        [@default true]
        (** with [matched_instance_forms_no_unknown_query], a piece is also
            asked its chain-join forms ([SeqInstantiation.chain_join_forms_of],
            after its matched forms): a positive existential whose sequence
            binder its body reads instantiated at the join
            [u ++ extract w 1 (len w - 1)] (or [extract u 0 i ++ w]) of two
            sequences free in the piece whose elements [u[i]] and [w[0]] the
            piece equates to a common term
            ([SeqInstantiation.chain_join_candidates_for]) -- the witness of
            a chain of states over a concatenation whose halves share their
            middle state -- its reads split, its universals skolemized, the
            rest matched.  Each form is a strengthening, so only a proof is
            read.  On by default *)
    chain_join_direct_reads_no_unknown_query : bool; [@default false]
        (** with [matched_instance_chain_join_candidates_no_unknown_query],
            two chains are also joined where the piece writes their shared
            element as one equation [u[i] = w[0]] between the two reads,
            with no common term ([SeqInstantiation.chain_join_direct_reads]).
            That is the shape the pairs take once the middle state, a field
            of a tuple, is a variable the one-point rule replaced by one of
            the reads (as after the preprocessor's
            [split_single_cons_clause_vars]).  Only which instances are
            offered changes, so only a proof is read.  Off by default *)
    matched_instance_assoc_open_no_unknown_query : bool;
        [@default true]
        (** with [matched_instance_forms_no_unknown_query], the matching that
            chooses a matched form's instances matches a concatenation
            pattern modulo associativity (a sequence binder standing for a
            run of the ground term's operands:
            [SeqInstantiation.assoc_concat_matching]), and an existential no
            complete substitution matches is instantiated at the maximal
            substitutions that fix every array and sequence binder, the
            scalar binders they leave out kept existential
            ([SeqInstantiation.open_scalar_matches]).  Every such instance
            implies its existential, so each form still only strengthens its
            piece and only a proof is read.  What it buys: a premise
            [forall s e r. P(h ++ s) /\ Q(s ++ [e], r) => P(h ++ s ++ [e])]
            whose ground facts write [h ++ [x] ++ y] is instantiated at
            [s = [x] ++ y], with the end state [r] that no ground term names
            left to the solver.  On by default *)
    matched_instance_last_index_candidates_no_unknown_query : bool;
        [@default true]
        (** with [matched_instance_forms_no_unknown_query], an integer binder
            of a positive existential is also offered [len s - 1] for each
            [seq.len s] of its body free in the piece
            ([SeqInstantiation.last_index_candidates_for]): the instance at
            the last index of a premise stated for every index.  Only which
            instances are offered changes.  On by default *)
    chain_join_focused_no_unknown_query : bool; [@default true]
        (** with [matched_instance_chain_join_candidates_no_unknown_query],
            the chain-join forms instantiate every existential left after the
            goal's instance at its two best substitutions, those whose
            instances write a term mentioning a constant the goal's
            skolemization introduced first (the per-index premise at the
            goal's fresh index, the transitivity law at the state it reads),
            then those writing the most terms of the piece, and keep no
            existential beside its instances.  A strengthening, so only a proof is read.
            On by default *)
    matched_instance_collections_only_no_unknown_query : bool;
        [@default true]
        (** with [matched_instance_forms_no_unknown_query], each piece is also
            asked, after its other matched-instance forms, with only the
            existentials binding an array or a sequence instantiated by
            matching and every other existential left as it is
            ([SeqInstantiation.matched_instance_form]'s [collections_only]):
            a premise universal over indices then stays for the solver to
            instantiate at the index the goal's instance leaves.  A
            strengthening of the piece, so only a proof is read.  On by
            default *)
    max_matched_form_size_no_unknown_query : int option;
        [@default Some 20000]
        (** with [matched_instance_forms_no_unknown_query], a matched-instance
            form whose instances are estimated (instances times body size, in
            formula nodes, summed over the existentials it instantiates, before
            any is built) past this many nodes is not built and is skipped as
            an undecided form is ([SeqInstantiation.max_matched_form_size]);
            [None] builds every form.  Skipping a form only loses a proof.
            20,000 nodes by default: over the Thrust inputs with the largest
            matched forms, every form of at most 160,000 characters was
            estimated at 12,300 nodes or fewer, while the two pieces that
            built three-million-character forms (13-31 s each) were
            estimated at 30,500 and 110,300 *)
    matched_bound_before_ranking_no_unknown_query : bool; [@default true]
        (** with [matched_instance_forms_no_unknown_query] and
            [max_matched_form_size_no_unknown_query], an existential's share
            of a matched-instance form's size estimate is tested against the
            bound before its substitutions are ranked
            ([SeqInstantiation.matched_bound_before_ranking]) rather than
            after: the ranking is a permutation, so the same forms are built
            and the same are skipped; only the time to skip one changes.  On
            by default *)
    ground_funapps_linear_no_unknown_query : bool; [@default true]
        (** with [matched_instance_forms_no_unknown_query], the ground
            function applications a matched-instance form matches against are
            collected in one pass that computes each node's variables outside
            the formula's free ones from its children's
            ([SeqInstantiation.ground_funapps_one_pass]), instead of one
            [Term.tvs_of] per application, which is quadratic in the nesting
            depth.  The same list either way, so the forms and the questions
            are the same; only the time to build them changes.  On by
            default *)
    max_chain_join_focus_size_no_unknown_query : int option; [@default None]
        (** with [matched_instance_forms_no_unknown_query], a chain-join form
            whose focused formula (the piece with the joined existential
            instantiated and the transitivity-law instances over every chained
            pair, before simplification) is past this many nodes is not built
            and is skipped as an undecided form is
            ([SeqInstantiation.max_chain_join_focus_size]); [None] builds every
            one.  Skipping a form only loses a proof.  Why: on Rust-derived
            pieces the focused formula and the simplification and matching
            run on it, before any instance estimate is reached, held the
            verdict for more than 200 s with no question asked *)
    fork_seqinst_questions_no_unknown_query : int option; [@default None]
        (** in the sequence instantiation of the zero-unknown verdict, ask each
            instantiated form in a forked copy of the process, killed after
            the larger of this many milliseconds and the question's own budget
            ([PCSatCommon.ForkedQuery]); [None] asks in-process.  Only a
            [`Valid] is read from such a question (a countermodel of an
            instantiated form says nothing about the clause), so a copy that is
            killed, or that cannot be forked, only loses a proof.  Why: one such
            question, quantifier-free and of about 13,000 nodes, was asked under
            a 10 s budget and had not returned 83 s later, when the run was
            killed: Z3's own budget does not hold on it *)
    fork_seqinst_kill_margin_no_unknown_query : int option; [@default None]
        (** with [fork_seqinst_questions_no_unknown_query], [Some m] kills a
            forked form at its own budget plus [m] milliseconds
            ([ForkedQuery.ladder_kill_ms]) instead of at the larger of that
            field's value and the budget, so that a short budget -- the first
            pass of [two_pass_budget_no_unknown_query] -- bounds a forked
            question as Z3's timeout bounds one asked in process, and [m]
            covers what the copy does besides the solver call (the fork, the
            conversion of the form, the copy's exit).  [None]: the larger of
            the two, as before.  Only the time an undecided question costs
            changes: a proof read from the copy is the solver's proof.  Why:
            with the field's value at 15,000 ms and a first-pass budget of
            5,000 ms, three undecided forms of one Rust-derived loop step each
            held the run 15.6 s, 48 s of the 54 s spent before the form that
            proved the clause in 1.8 s *)
    lemma_application_ms_no_unknown_query : int option; [@default Some 2000]
        (** in the sequence instantiation of the zero-unknown verdict, a piece
            nothing else proved is given to [PCSatCommon.LemmaApplication]:
            its quantified hypotheses (a lemma the clause calls, the negated
            goal) are instantiated at matched terms, each disjunct of an
            instance is asked about alone, under this many milliseconds, and
            dropped when the facts refute it; a hypothesis left with one
            disjunct adds it as a fact, and one left with none proves the
            piece.  [None] asks nothing; the default is 2000.  Only proofs of
            validity are read.
            Why: a lemma applied at the premises' witnesses and a goal at the
            lemma's joined index map were each decided in about 0.1 s per
            disjunct, while every form asked whole, and the same instances
            asked as one question, were left undecided at 30 s by z3 and
            cvc5. *)
    guarded_facts_ms_no_unknown_query : int option; [@default Some 3000]
        (** in the quick sweep and the rewritten stages of the zero-unknown
            verdict, a piece (or a
            clause asked whole) whose negation holds a hypothesis
            [forall xs. not B(xs) \/ ...] with a guard [B] that a fact [B(ts)]
            matches is first given to [PCSatCommon.GuardedFacts]: the
            single-constructor variables it reads through selectors split into
            their fields, the hypothesis applied forward at [ts] (a disjunct the
            facts over its own variables refute dropped, the one left kept as a
            fact), and the strengthened question asked -- all in a forked copy
            killed after this many milliseconds, with the bit-vector rewrite of
            bounded integers off in the copy.  Only a proof is read; anything
            else falls through to the piece's own question.  Each question is
            tried once per process.  [None] (the default): nothing is tried.
            Why: on a Rust-derived bit-set postcondition (the word index and
            mask a call returned, read through a tuple, and the relation fixing
            the element's index) every form of the ladder was left undecided at
            10 s, while the tuple split with the contract's conclusion
            derived as a fact at the relation's point was decided in 0.1-0.3 s;
            with the contract's instance asserted as the implication it is, or
            with the tuples unsplit, Z3 left it undecided at 20-30 s *)
    guarded_facts_theory_facts_only_no_unknown_query : bool;
        [@default true]
        (** with [guarded_facts_ms_no_unknown_query], a form whose derived
            facts are all reads of a relation (a Boolean [select] chain, a
            variable or a function application said to hold or fail) is not
            asked, and the piece is asked as without the rule.  Such a form
            is the question plus ground atoms of the relations its own
            hypotheses are guarded by.  Why: over five Rust-derived inputs no
            such form was decided where the question alone was not (each form
            and question replayed in z3 at 10 s): the decided ones were decided
            as fast without the facts, the others were undecided questions, and
            each undecided form held the forked copy for its whole budget --
            15-20 s of a loop-closure input that answers at 86-103 s of 120;
            the forms that proved what the question did not all derived a fact
            with arithmetic content.  [false] (the default): every form is
            asked. *)
    lemma_application_rlimits_no_unknown_query : (int * int) option;
        [@default Some (300000, 500000)]
        (** with [lemma_application_ms_no_unknown_query], [Some (native,
            fallback)] bounds each of the route's questions by a Z3 resource
            count ([rlimit], the solver's own steps, the same whatever the
            host's load): [native] per question as asked, [fallback] per
            question of the sequence-axiom fallback asked after an undecided
            one; the route's milliseconds then stay as the kill of both (the
            fallback's wall-clock budget is raised to them from the
            process-wide one), so that what decides a question is its count
            and the wall clock only stops a check the count does not stop.
            An exhausted count is an undecided question, which the route reads
            as "not refuted", as it reads a timeout.  [None]: wall clock only.
            Why: on a Rust-derived filter's transitivity piece the route's
            questions split cleanly -- every refutation the route used took at
            most 37,347 units (under 0.1 s), every native question it did not
            decide ran to the 2000 ms budget (1.0-1.4 million units), and the
            fallback proved at 27,563 and 204,943 units where the questions it
            did not prove ran to its 500 ms budget (437,589-583,927 units) --
            so the undecided ones were 27 of the route's 36 s at load 8, and
            under load the fallback's 205k-unit proof came near its 500 ms *)
    fork_invalid_skips_seq_axiom_fallback_no_unknown_query : bool;
        [@default false]
        (** a zero-unknown ladder question asked in a forked copy
            ([fork_seqinst_questions_no_unknown_query],
            [fork_refused_questions_no_unknown_query]) and answered invalid
            there is not handed to the sequence-axiom fallback, as an
            in-process question answered invalid is not: the copy's
            countermodel is not sent back, so without the field its answer
            reaches the fallback as an undecided one.  The fallback can only
            turn an undecided answer into a proof, and a question with a
            countermodel has none to give, so only the time changes.  Why: on
            a Rust-derived input under a resource-counted fallback, each such
            question spent another 1-2 s in a fallback that proved none of
            them, about 20 s of one clause's 21 s *)
    ladder_seq_axiom_rlimit_no_unknown_query : (int * int) option;
        [@default None]
        (** [Some (units, kill_ms)]: every question of the zero-unknown
            ladder asks its sequence-axiom fallback under a Z3 resource count
            of [units] ([Z3interface.with_seq_axiom_rlimit]), its wall-clock
            budget raised (or lowered) from the process-wide
            [seq_axiom_fallback] to [kill_ms], which then only stops a check
            the count does not stop (the question's own budget still caps
            it).  An exhausted count is an undecided fallback, which leaves
            the question's answer as it was: only a proof comes out of the
            fallback.  [None]: the process-wide wall-clock budget alone.  Why:
            on a Rust-derived loop step the fallback's proofs of seven
            near-identical pieces took 0.37-0.74 s against its 500 ms budget,
            so the host's load decided how many of the seven were proved
            (seven in one run, three in the next), and each piece lost cost
            another 12-20 s of larger forms *)
    ladder_seq_axiom_rlimit_refused_only_no_unknown_query : bool;
        [@default false]
        (** with [ladder_seq_axiom_rlimit_no_unknown_query], the pair applies
            only to the fallback of a fresh ladder question the solver was
            not asked at all -- [may_not_return] refused it and no forked
            copy asked it ([fork_refused_questions_no_unknown_query] off) --
            for which the fallback is the question's only attempt
            ([LadderSeqAxiomRlimit.for_fallback]); the fallback after a
            question the solver was asked and left undecided, and every
            fallback asked inside the pooled questions' [check_valid], keep
            the process-wide wall-clock budget, as without the pair.  The
            fallback turns nothing but an undecided answer into [`Valid], so
            only which undecided questions are proved, and what each costs,
            changes.  Why: over four Rust-derived inputs every fallback proof
            of a fresh question the solver had been asked was cheap (at most
            0.2 s), and on one loop step the 17 fallbacks after questions the
            solver had run to their budget proved nothing and cost 51 s under
            a 3 s kill, where the process-wide 500 ms would have cost 8.5 s *)
    ladder_seq_axiom_units_per_node_no_unknown_query : int option;
        [@default None]
        (** with [ladder_seq_axiom_rlimit_no_unknown_query] = [Some (units,
            kill_ms)], [Some k] makes the fallback's count of a fresh ladder
            question of [n] nodes [k * n] rather than [units], and gives a
            question the count only where [k * n] reaches [units]; a smaller
            question keeps the process-wide wall-clock budget, as without the
            pair ([LadderSeqAxiomRlimit.for_fallback]).  So a large question
            is given a count in proportion to its size, killed at [kill_ms],
            and a small one stops when it stopped before.  [None]: the fixed
            count [units] for every question.  The fallback turns nothing but
            an undecided answer into [`Valid], so only which undecided
            questions are proved, and what each costs, changes.  Why: over
            four Rust-derived inputs (125 fallback questions of the ladder,
            each asked with a 3 s or 1 s kill) the questions the fallback
            proved needed at most 135 units per node of the question except
            five of under 1,600 nodes (at most 0.71 s each), while those it
            did not prove ran at 170-40,000 units per node until stopped, the
            large ones at 5-50; so a count of 64 units per node is above
            every proof of a large question -- seven 22,900-node pieces of
            one loop step needed 650,000-1,120,000 units, 0.33-0.54 s against
            the 500 ms that load decided -- while a fixed count of 1,500,000
            units let small unproved questions run 1-3 s instead of 0.5 s,
            8-17 s more a run on three other inputs *)
    lemma_application_before_cvc5_no_unknown_query : bool; [@default true]
        (** ask a piece no form proved of the lemma application
            ([lemma_application_ms_no_unknown_query]) BEFORE the cvc5 retry
            ([ladder_cvc5_retry_ms_no_unknown_query]) rather than after it;
            each reads only a proof, so the order changes the time a piece
            costs, never what is proved of it.  Why: on a Rust-derived
            filter's pieces the route proves, the cvc5 retry ran first and
            answered [unknown] after 6.6-7.4 s each (16.5 s of a run at load
            8), while the route's own refutations take well under a second *)
    lemma_application_after_form_timeout_no_unknown_query : bool;
        [@default true]
        (** ask a piece of the lemma application
            ([lemma_application_ms_no_unknown_query]) as soon as one of the
            piece's forms has run out of its budget, before its later forms
            (with [two_pass_budget_no_unknown_query], between the two passes
            when a form was deferred), instead of after every form.  A piece
            some form proves before any form runs out is asked exactly as
            without it; each step reads only a proof, so only the time a piece
            costs changes.  Why: on a Rust-derived filter's iterator law, which
            the route proves in a few seconds, three of the piece's thirteen
            forms ran to the 10 s budget, 34 s of the 37 s its forms cost *)
    lemma_goal_first_probe_no_unknown_query : int option; [@default None]
        (** [Some n], with [lemma_application_extended_no_unknown_query]: a
            piece some of whose goal pieces have a witness goal that only the
            last-witness-disjunct rule finds is first given a short extended
            goal-first probe of at most [n] questions per goal piece, before
            the plain route ([PCSatCommon.LemmaApplication.goal_first_probe]).
            Only the order and the caps change; only proofs are read.  Why:
            on a loop step the plain route spent all 64 of its questions
            (35-60 s) where the extended route then proved the piece in 11. *)
    lemma_application_extended_no_unknown_query : bool; [@default false]
        (** with [lemma_application_ms_no_unknown_query], the extended route
            ([PCSatCommon.LemmaApplication.extended]): a conclusion that is a
            conjunction split into one piece per conjunct, each piece's
            negated goal tried first; the existential facts opened; a
            sequence binder offered the one-step extensions [g ++ [e]] of the
            facts' sequences, and the instances that build their terms tried
            first; a disjunct the facts leave undecided asked again by cases
            (an existential's disjunctive body distributed, an index split
            against a concatenation's prefix), each with selections of the
            facts, smallest first.  Only proofs are read, as without it.
            Why: a loop step whose witness extends the invariant's history by
            the one item [next] produced was undecided whole by z3 and cvc5,
            with the witness given too, while each case, asked beside the two
            or three facts about its terms, was decided in under a second. *)
    ladder_cvc5_retry_ms_no_unknown_query : int option; [@default Some 20000]
        (** in the sequence instantiation of the zero-unknown verdict (and
            wherever its forms are asked: the validator's read-back ladder and
            the Houdini pre-pass's sequence route), a piece none of its forms
            proved is asked once more, after its last form: its largest form
            built ([SeqInstantiation.best_built_form]) is given to cvc5 as a
            separate process with this many milliseconds of its own budget and
            killed by the wall clock one second later
            ([PCSatCommon.Cvc5Proof.valid_within]).  Only cvc5's [unsat] of the
            negation is read, as a proof of the form and so of the piece; its
            [sat] is never a refutation (its models are not checked here), and
            anything else leaves the piece undecided as before.  [None] asks
            nothing.  Why: a form of a Rust-derived produces-transitivity piece
            that Z3 left undecided at 30 s was proved by cvc5 in 3.5-15 s.
            On by default *)
    weaken_refused_questions_no_unknown_query : int option; [@default None]
        (** a fresh-context validity question of the zero-unknown verdict that
            [may_not_return] refuses is first handed, with this many
            milliseconds (capped by the question's own budget), to its weakened
            form: the negation's top-level conjuncts [may_not_return] refuses
            (those binding a sequence under a quantifier) are dropped and the
            rest is asked in-process ([WeakenedQuery.rest_unsat]).  Only an
            [unsat] of the rest is read, as [`Valid]; anything else leaves the
            question as it is without this field (refused, or forked under
            [fork_refused_questions_no_unknown_query], then the sequence-axiom
            fallback).  [None] asks nothing.  Why: on five sequence inputs
            that otherwise go unanswered the ladder refused 182 questions and the weakened form
            proved 97 of them valid, none invalid *)
    ladder_cvc5_rlimit_no_unknown_query : int option; [@default None]
        (** with the cvc5 retry above, also give cvc5 a budget of this many of
            its own resource units ([--rlimit-per]); cvc5 answers [unknown]
            when they are spent, which leaves the piece undecided as any other
            non-proof does.  Unlike the budget in milliseconds, the count does
            not depend on the machine's load, so the same question gets the
            same chance on an idle and on a busy machine; the milliseconds stay
            as cvc5's time limit and the wall-clock kill.  [None] passes no
            resource limit *)
    ladder_proof_shortcuts_no_unknown_query : bool; [@default true]
        (** two exact shortcuts in front of solver calls whose answer is
            already known.  (1) A form of the sequence instantiation (in every
            route that asks its forms) that is literally [true] is proved
            without being asked ([SeqInstantiation.true_forms_proved]), and so
            is a literally [true] formula handed to the cvc5 retry.  (2) The
            cvc5 retry answers a text it has already had [unsat] or [sat] to,
            in this process, from that answer ([PCSatCommon.Cvc5Proof.
            shortcuts]; a forked copy keeps what was recorded before its
            fork).  Both give the answers asking would give: [true] is valid
            in every model, and cvc5 is deterministic on one text, so only
            budget cuts, which say nothing about a form, are skipped.  Why:
            on six Rust-derived inputs ten of 27 cvc5 retries were of a form
            that was [true], left unproved by an asker whose budget was cut,
            and one 46,467-unit text was sent four times in one run.  On by
            default *)
    fork_refused_questions_no_unknown_query : int option; [@default None]
        (** a fresh-context question of the zero-unknown verdict that
            [may_not_return] refuses (a quantifier binding a sequence) is asked
            all the same, in a forked copy killed after the smaller of this many
            milliseconds and the question's budget, and only a [`Valid] is read
            from it; [None] refuses it as before.  The smaller, because every
            refused question then costs its kill: at the 10 s budget the
            rewritten stage of one input spent 90 s on nine refused pieces,
            none proved, where refusing them took 0.6 s each.  The sequence-axiom fallback
            still follows an undecided answer.  Sound for the reason the fork of
            [fork_seqinst_questions_no_unknown_query] is: the copy's proof is
            the solver's proof, and anything else is undecided.  Why: on a
            Rust-derived input a refused piece of the rewritten stage is proved
            by Z3 in 2.5 s when asked, while the forms that replace it time out
            at 12 s *)
    seqinst_max_int_input_nodes_no_unknown_query : int option; [@default None]
        (** in the sequence instantiation of the zero-unknown verdict, a
            piece's deep form is not built when the formula its integer step
            would instantiate is past this many nodes
            ([SeqInstantiation.piece_max_int_input_nodes]); [None] builds every
            one.  Not building a form only loses a proof.  Why: that step did
            not return in 45-70 s on forms of 80,000 and 270,000 nodes, the
            silent stretch that ended two Rust-derived inputs' runs, while the
            deep forms proved on them were under 20,000 nodes *)
    seqinst_max_nodes_no_unknown_query : int option; [@default None]
        (** in the sequence instantiation of the zero-unknown verdict, the node
            budget of each piece's plain and deep instantiations
            ([SeqInstantiation.piece_max_nodes]); [None] bounds nothing but the
            per-quantifier limits.  A bounded instantiation is still a
            strengthening of the piece, so the bound only loses proofs.  Why: on
            two Rust-derived inputs the verdict went silent for 60-100 s while
            the first deep form of one piece was being built, no question
            asked, until the run was killed *)
    matched_instance_aligned_hyps_no_unknown_query : bool; [@default true]
        (** with [matched_instance_forms_no_unknown_query], the earlier-pieces
            form first aligns each earlier piece with the piece, mapping its
            own variables onto the piece's by matching disjunct against
            disjunct and dropping the disjuncts so matched
            ([SeqInstantiation.aligned_hypotheses]), and then keeps every
            existential over no array or sequence and every universal for the
            solver to pair, the goal's index with a hypothesis's among them.
            Sound because the pieces before are proved first.  Off by
            default *)
    chain_focus_form_no_unknown_query : bool; [@default true]
        (** in the sequence instantiation of the zero-unknown verdict, after
            every other form of a piece has failed, also ask it with a
            positive sequence existential [exists x. ... h(s, x, e) ...]
            instantiated at [x0 ++ x1] ALONE, for a pair of ground
            applications [h(s, x0, m)] and [h(m, x1, e)] of the piece, a
            sequence existential two of whose applications of [h] match that
            pair (a negated transitivity law) instantiated at the matched
            tuple alone, and every other sequence existential replaced by
            [false]; once with the integer binders left bound and once with
            them instantiated.  Sound for validity only: each instance
            implies its existential and [false] implies anything, so the form
            implies the piece.  Off by default *)
    chain_focus_push_witnesses_no_unknown_query : bool; [@default true]
        (** in the chain-focused forms ([chain_focus_form_no_unknown_query]
            and the pushed forms below), the chain-focused
            existential's OTHER sequence binders are instantiated too, each
            binder [y] the body reads at the focused binder's length ([t =
            seq.nth y (seq.len x)]) at [a ++ unit t], [a] the premise
            sequence whose length a premise ties to the chain's prefix (a
            loop's history restated after a step: the previous history
            pushed once, [SeqInstantiation.push_witnesses]); and each such
            focused form, with the premise laws over opaque values kept
            quantified and its integer binders instantiated, is asked FIRST
            among the piece's forms (at most two).  Sound for validity only:
            every instance implies its existential and keeping a disjunct is
            exact, so each form implies the piece.  Off by default *)
    lazy_plain_form_no_unknown_query : bool; [@default true]
        (** in the sequence instantiation of the zero-unknown verdict, build
            a piece's plain instantiation only when that form is asked
            ([SeqInstantiation.lazy_plain_form]), not when the piece's forms
            are listed (every piece of a clause, before grouping).  The same
            forms in the same order; only when each is built changes (and
            with it the order of fresh-name draws).  On by default: the
            eager listing built every piece's plain instantiation (1-3 s a
            piece under load) although that form comes late and is rarely
            asked, which spent most of a 120 s budget before any question *)
    case_split_index_forms_no_unknown_query : bool; [@default true]
        (** in the sequence instantiation of the zero-unknown verdict, ask
            each of the first two forms of a piece that reads [seq.nth (u ++
            w) i] at [i = t] or [t + c] ([t] a free integer, the skolem of a
            position of an extended history) first by the three cases of [t]
            against [len u] ([SeqInstantiation.index_cases_outcome]: the form
            with [t >= len u], [t != len u], [t <= len u] added as a
            disjunct), and whole only when some case is not proved; once a
            case question of a piece is left undecided (it ran out of its
            budget), the piece's forms are asked only whole.  Sound: the
            cases cover every model, so the three proved prove the form, and
            the form implies the piece.  On by default, together with the size
            ratio below *)
    case_split_index_budget_no_unknown_query : int option; [@default None]
        (** with [case_split_index_forms_no_unknown_query], ask each index
            case question at this budget in ms (capped at
            [no_unknown_query_timeout]) instead of the form's own, so that a
            case the solver decides only slowly counts as undecided and the
            piece's forms are then asked whole
            ([SeqInstantiation.index_case_ask]).  Only when a proof is found
            changes: the cases are still all proved for a proof by cases,
            and a form not so proved is asked whole at its own budget.  Why:
            on a loop-step clause whose whole form is proved in about 11 s,
            each of its three cases was proved in 10.6-14.3 s, tripling its
            cost, while on the input the cases are for each case decides in
            0.1-0.2 s.  [None] (the default) asks the cases at the form's
            budget *)
    case_split_index_max_size_ratio_no_unknown_query : float option;
        [@default Some 0.5]
        (** with [case_split_index_forms_no_unknown_query], ask a candidate
            split by cases only when each of its three case questions has an
            AST size at most this ratio times the form's, skipping it with no
            question otherwise ([SeqInstantiation.index_case_max_size_ratio]);
            a form none of whose candidates passes is asked whole, as
            without the cases.  Only removes case questions, so a proof by
            cases is still three proved cases.  Why: where a case decides
            the guards of most of the form's reads its question is a few
            percent of the form's size and decided fast; where it does not,
            each case question keeps most of the form's size and is about as
            slow as the whole form, tripling the piece's cost.  [None] asks
            every candidate; the default is 0.5 *)
    chain_assoc_match_no_unknown_query : bool; [@default true]
        (** as [chain_focus_form_no_unknown_query], for a positive sequence
            existential whose body applies [h] with [v ++ t] in the middle
            ([v] bound by it) and a pair [h(a, u, b)], [h(b, w, c)] of ground
            applications whose start and end match the application's: [u ++
            w] is matched against [v ++ t] modulo associativity (so [v] is [u
            ++ w'] with [w = w' ++ t], the end bound to [c]), the existential
            is instantiated at that match alone and a transitivity law at the
            pair.  Sound for validity only, for the same reason.  Off by
            default *)
    prepend_unit_candidates_no_unknown_query : bool; [@default true]
        (** in the sequence instantiation of the zero-unknown verdict, also
            offer a positive sequence existential whose body builds
            [x ++ p1 ++ ... ++ pk] the terms [unit e ++ u], where [u] is what
            a clause term [u ++ q1 ++ ... ++ qk] leaves for [x] and [unit e] a
            singleton of the clause: a law at a state one step later, after
            the step produced the item [e].  Sound as the other instances are:
            each implies the existential, so only a proof of validity is
            read.  Off by default *)
    pointwise_concat_candidates_no_unknown_query : bool; [@default true]
        (** in the sequence instantiation of the zero-unknown verdict, also
            offer a positive sequence existential read pointwise and mentioning
            a clause sequence [w1 ++ ... ++ wm] the terms [u1 ++ ... ++ um],
            each [u_i] read beside [w_i] at one index in an atom of the clause
            (the premise [forall k. R(u_i[k], w_i[k])]); an element bound by a
            premise's universal is a candidate only with
            [skolemize_positive_universals_no_unknown_query].  Sound as the
            other instances are: each implies the existential.  Also splits a
            piece whose distribution over its disjunctions would exceed the
            piece bound along one side of the disjunction, the other kept
            whole, which is exact.  Off by default *)
    share_premise_instances_no_unknown_query : bool; [@default false]
        (** in the sequence instantiation of the zero-unknown verdict, ask a
            clause of several pieces first as the pieces of ONE instantiation
            of the whole clause, which is then quantifier-free, so the split
            is exact, before instantiating every piece on its own; the premise
            disjuncts the pieces share are instantiated once instead of once
            per piece.  Sound as the other forms are: the whole clause's
            instantiation strengthens it, and only a proof of validity is
            read.  When it does not prove the clause the pieces are asked as
            without it, so it costs time and never an answer.  Off by
            default: on the one input measured the shared forms were larger
            and the first undecided *)
    group_piece_forms_no_unknown_query : bool; [@default true]
        (** in the sequence instantiation of the zero-unknown verdict, ask the
            first forms of consecutive pieces of one clause as ONE question
            before asking each piece's forms: the forms, renamed so that the
            premise disjuncts they repeat coincide, with their common
            disjuncts factored out ([SeqInstantiation.PieceGroups]).  The
            question is equivalent to the conjunction of the renamed forms,
            each of which is valid exactly when its form is, so only a proof
            of validity is read and it proves every piece of the group; when
            the question is not proved, each piece is asked its forms as
            without the switch, the first being the same one, so it costs
            time and never an answer.  On by default: over 198 sequence and
            array inputs at 120 s, together with the switch below, it gained
            an input no run answered without it (6 of 6 against 0 of 6) and
            lost none *)
    split_int_binders_at_ite_no_unknown_query : bool; [@default true]
        (** every validity question the zero-unknown verdict asks through
            [Z3interface.check_valid], [check_valid_seq_as_array] or the
            sequence-axiom fallback (the lemma route's included) is first
            rewritten with each integer binder whose body holds an [ite] on
            [x < c] (alone, or inside a compound condition such as the range
            tests a read of a concatenation is split with) split at [c] and
            its upper part shifted to start at zero
            ([Z3interface.with_split_int_binders], [IntBinderSplit.rewrite]).
            Exact: each split is an equivalence in every model, so every
            answer means what it meant.  Why: a proof that needs a universal
            at [x := k + c] from a read at [x - c] was found only by
            model-based instantiation, whose success depended on the spelling
            of a generated sort name or of bound variables and on the seed.
            On by default *)
    arith_solver_no_unknown_query : int option; [@default None]
        (** Z3's [smt.arith.solver] for every pooled question the zero-unknown
            verdict asks ([Z3interface.with_arith_solver]): [Some 2] asks them
            with the simplex-based [theory_arith] instead of the default
            [lp]-based [theory_lra], on instances of their own.  The questions
            are the same, so only their time, and whether one outside the
            decidable fragment is decided, can change.  [None], the default,
            leaves the parameter unset. *)
    group_question_max_nodes_no_unknown_query : int option; [@default Some 380000]
        (** with [group_piece_forms_no_unknown_query], a grouped question
            larger than this many formula nodes, as it would be asked, is not
            asked, and its group's pieces are asked their own forms at once,
            as after a grouped question that is not proved
            ([SeqInstantiation.group_question_max_nodes]); [None] asks every
            one.  Only a proof is read from a grouped question, so this
            changes which questions are asked and never which answer is
            read.  Why: one grouped question of 570,000 nodes was held by Z3
            for 44 s under a 10 s budget and left the run no time for the
            per-piece forms that prove its pieces, while the grouped
            questions proved on the same inputs were under 90,000 nodes.
            On by default. *)
    share_piece_simplify_no_unknown_query : bool; [@default true]
        (** with [group_piece_forms_no_unknown_query], group the pieces'
            first forms before their last simplification and simplify each
            grouped question once ([SeqInstantiation.share_piece_simplify]),
            so that the disjuncts the pieces share are simplified once per
            group instead of once per piece.  The question is equivalent in
            every model to the one asked without it, but not the same
            formula; a piece whose group is not proved is asked its own
            forms as without it.  Inert without the grouping switch.  On by
            default, measured together with it *)
    share_replayed_int_instances_no_unknown_query : bool; [@default false]
        (** inside the replay of fresh names under which a clause's pieces
            have their first deep forms built for grouping, let the integer
            step reuse the instances of an existential met again with the
            same candidates, budget left and replay position
            ([SeqInstantiation.share_replayed_int_instances]).  Each form is
            the formula built without it, name for name, so the questions
            asked are the same; only the building time changes.  Why: the 64
            pieces of a Rust-derived clause share their premise, and its
            integer instances were built once per piece, 11 s of a 120 s
            budget.  Off by default: to be measured *)
    share_deep_shapes_no_unknown_query : bool; [@default true]
        (** build the first deep form of the pieces of one clause that differ
            only in small quantifier-free literals no step of the deep form
            reads (no sequence, array or opaque-sort subterm, no binder) once
            per premise part and replay position, with a placeholder for the
            literals, and give each piece that form with its own literals put
            back where the simplification of the whole piece puts them
            ([SeqInstantiation.share_deep_shapes]).  Each form is the formula
            built without it, with the same fresh names drawn, so the
            questions asked are the same; a piece whose literals the
            simplification could merge with the premise part is built as
            without it.  Why: a Rust-derived loop-body
            clause has 64 pieces in families of eight sharing their premise
            part, and their first deep forms, 139,000-307,000 nodes each,
            took 75 s of a run at load 14.  Off by default: to be measured *)
    remember_proved_pieces_no_unknown_query : bool; [@default true]
        (** a schedule for the zero-unknown verdict's clause-by-clause
            stages that keeps what one stage proved for the next ones and
            lets no clause or piece end a stage for the others:
            - a rewritten clause asked by its pieces (the early and the late
              rewritten passes) is asked EVERY piece, not only those up to the
              first undecided one; a piece refuted still refutes at once, and
              when a piece stays undecided the whole clause is asked last, as
              without the switch;
            - the pieces left undecided are remembered, and the later
              rewritten pass and the sequence instantiation ask the
              conjunction of those pieces in place of the rewritten clause
              (the clause is the conjunction of its pieces in every model, so
              the clause is valid once the remembered pieces are) -- only
              when some piece was shown valid: with every piece undecided
              that conjunction is the clause again, in a form the sequence
              instantiation splits worse, and the clause is kept;
            - the sequence instantiation asks every clause not yet shown
              valid, smallest first by formula size (ties in the clauses'
              order), records each it proves, and does not stop at the first
              it cannot prove.
            Only a proof is read from the new questions and a refutation is
            taken only where it was before (a piece of a rewritten clause
            refuted, which refutes the rewritten clause), so the switch
            changes which answer is reached within the time and never which
            answer is right.  What it buys: a 32-piece clause whose second
            rewritten piece the sequence-axiom fallback decided in one run
            and not in another went whole, in the second, to the sequence
            instantiation, where every piece took about 27 s; the other
            pieces had each been decided in 0.1 s in the rewritten form.
            On by default *)
    pin_seq_lengths_no_unknown_query : bool; [@default true]
        (** when preprocessing leaves no predicate variable and the validity
            questions end undecided or out of budget, also look for a
            refutation with every free sequence variable fixed to a literal of
            length 0, then 1, then 2 ([NoUnknownSeqPin]); it can only turn
            [unknown]/[timeout] into [unsat], never into [sat]: a model violating
            the clause with a sequence fixed to a literal violates the clause.
            On by default: with [split_seq_reads] in the preprocessor it
            refutes a nested-sequence Thrust query that no other setting
            decides.  When off, nothing is asked beyond the existing
            questions *)
    pin_seq_lengths_from_model_no_unknown_query : bool; [@default true]
        (** with [pin_seq_lengths_no_unknown_query], first, clause by
            clause, take each free sequence's length from a model of the
            quantifier-free relaxation of the clause's negation (its quantified
            parts replaced by [true]), at most 32, and ask the clause's
            negation strengthened by those length equations, before the fixed
            lengths 0, 1, 2.  Up to two more questions per clause; a
            refutation is still only a model of a strengthening of the
            negation, so it can only turn [unknown]/[timeout] into [unsat].
            The relaxation's model is read for lengths and for nothing else *)
    sweep_unknown_free_clauses : bool; [@default false]
        (** when preprocessing leaves predicate variables, first ask every
            clause that mentions none of them, piece by piece, under the
            budgets of [quick_sweep_no_unknown_query] ((500, 5000) when that
            is [None]); a piece shown invalid refutes the problem at once,
            with its countermodel.  Asked once per solve, before the loop *)
    prove_unknown_free_clauses_first : bool; [@default true]
        (** when preprocessing leaves predicate variables and some clauses
            mention none of them, first decide those clauses alone as a
            problem with no unknown, through the whole zero-unknown verdict
            (its sequence instantiation, pins and retries).  Proved valid:
            they are dropped, and the loop runs on the rest.  Refuted: the
            problem is answered [unsat] with that refutation.  Undecided: the
            loop runs on the whole problem as without the switch.  Asked
            once per solve, before the sweep and the loop *)
    prove_unknown_free_clauses_first_budget_ms : int option; [@default Some 60000]
        (** with [prove_unknown_free_clauses_first], [Some ms] runs the pass
            in a forked copy of the process killed after [ms] milliseconds of
            wall clock, so it costs at most that (plus the fork) on an input
            where it decides nothing; a killed or failed copy is the undecided
            case.  A refutation found in the copy is answered [unsat] without
            a certificate, or, when one is asked for, the pass is run again in
            this process to build it.  [None]: the pass runs in this process
            with no bound but the ladder's own per-question budgets *)
    prove_unknown_free_clauses_first_in_process_when_large : bool;
        [@default false]
        (** with [prove_unknown_free_clauses_first_budget_ms = Some ms], the
            pass is run in this process, under a strict deadline of [ms],
            instead of in a forked copy whenever the fork's copy-on-write
            cost does not fit: when this process's major heap is larger than
            the least headroom ([memory.max - memory.current]) of its memory
            cgroups ([Common.ForkGuard.fork_fits]).  A forked OCaml copy
            writes every page of the live heap while its collector marks, so
            it can hold a second copy of the heap; past the headroom that
            copy is what a memory cap kills.  In process the pass asks the
            same questions; the deadline is read at phase boundaries, so it
            can overrun [ms] by one phase where the copy was killed on time,
            and an answer the deadline cuts is the undecided case, as a killed
            copy's is.  With no readable limit the copy is made as before *)
    prove_unknown_free_clauses_first_within_deadline : bool; [@default true]
        (** with [prove_unknown_free_clauses_first_budget_ms = Some ms],
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
    pin_scalars_no_unknown_query : bool; [@default true]
        (** when preprocessing leaves no predicate variable and every question
            above, the sequence-length pin included, leaves the answer
            [unknown]/[timeout], also look for a point of a clause's free
            variables at which the clause is PROVED false in every model
            ([NoUnknownScalarPin]): a point guessed from a quantifier-free
            relaxation of the clause's negation, then the negation at that
            point proved valid by the sequence instantiation.  It can only turn
            [unknown]/[timeout] into [unsat].  Built for a clause whose
            sequences are all bound and whose countermodel is an integer
            point *)
    pin_relations_no_unknown_query : bool; [@default true]
        (** when preprocessing leaves no predicate variable and every question
            above, the point pin included, leaves the answer
            [unknown]/[timeout], also look for a countermodel of a clause whose
            free variables include Boolean-valued arrays (universally
            quantified relations) with those arrays fixed to the finite
            relations the clause's own facts and laws generate
            ([NoUnknownRelationPin]); the pinned negation is asked for
            satisfiability and only a model is read, so it can only turn
            [unknown]/[timeout] into [unsat].  It runs only after the point
            pin has found nothing, so no answer reached without it can be
            reached any later with it *)
    early_pins_no_unknown_query : bool; [@default true]
        (** when preprocessing leaves no predicate variable, also ask the
            sequence-length, point and relation pins (the three fields above)
            once right after the quick sweep, before the rewritten forms and
            the sequence instantiation, on the clauses not yet shown valid,
            under [early_pins_budget_no_unknown_query]; a refutation found
            there is returned as the late pins' is, and otherwise the ladder
            continues unchanged, the late pins included.  It changes only the
            time at which a pin's answer is reached, never the answer.  On
            by default; built for a Thrust input whose point pin refutes it
            only at the end of the ladder, near the run's budget *)
    early_pins_stop_at_deadline_no_unknown_query : bool; [@default true]
        (** with [early_pins_no_unknown_query], stop the early pins once the
            whole budget of [early_pins_budget_no_unknown_query] has elapsed,
            before building the next clause's, piece's or relaxation's
            question, and build a point or relation pin's relaxations one at
            a time rather than all at once.  Without it the deadline only
            stops questions from being asked, while the pins go on building
            the relaxations they would ask -- two sequence instantiations per
            piece, each measured at 17-25 s on a Rust-derived map-extension
            clause, where two such inputs spent 78 and 94 s in early pins of a
            10 s budget.  Only the early pins are cut short, and they read
            only a model of a pinned negation or a proof, so this changes
            when the ladder moves on, never an answer: the late pins still
            run in full.  On by default *)
    early_pins_budget_no_unknown_query : int * int; [@default (1000, 10000)]
        (** [(per question, whole)] in milliseconds for the early pins: each
            question gets at most the first, and none is asked once the
            second has elapsed since the early pins began *)
    early_relation_pin_budget_no_unknown_query : (int * int) option;
        [@default None]
        (** [Some (per question, whole)] in milliseconds: with
            [early_pins_no_unknown_query], the EARLY relation pin gets a budget
            of its own, which starts when that pin starts, instead of what the
            sequence-length and point pins before it have left of
            [early_pins_budget_no_unknown_query].  Under the shared budget
            those two pins can spend all of it, and the relation pin then
            builds its shapes and asks none of them, or asks its shape guesses
            under a one-second cap that a loaded machine overruns, which ends
            the shape search for that length sum.  The late relation pin is
            unchanged.  The relation pin returns at once on a clause with no
            Boolean-valued array among its free variables, so the budget is
            spent only where a relation can be pinned.  A pin reads only a
            model of a strengthened negation, so this changes when a
            refutation is reached and which questions are asked before it,
            never an answer.  Built for a Rust-derived input refuted only by
            the late relation pin near the end of a 120 s run; off by
            default: to be measured *)
    early_relation_pin_cpu_clock_no_unknown_query : bool; [@default false]
        (** with [early_relation_pin_budget_no_unknown_query], charge that
            budget by the CPU time of the thread running the pin instead of
            by the wall clock ([NoUnknownLadder.cpu_budget]): the whole budget
            is CPU milliseconds, and each question's cap, which the solver
            takes in wall time, is the per-question CPU budget times the
            wall-over-CPU slowdown the pin has seen so far (at most
            [early_relation_pin_max_scale_no_unknown_query]), the whole stage
            being cut off at that many times the whole budget in wall time.
            On a loaded machine the pin's wall time is a multiple of its CPU
            time -- each question, and the full major collection forced
            before each fresh solver context, waits for a processor -- so a
            wall-clock budget ran out, or a shape guess hit its cap and ended
            the search at its length sum, before the shape that refutes was
            reached, on a Rust-derived input the pin refutes in about 10 s of
            CPU time.  The questions are the same and asked in the same
            order; only how far down the list the budget reaches changes, so
            this changes when a refutation is found, never an answer.  Off by
            default *)
    early_relation_pin_max_scale_no_unknown_query : float; [@default 6.]
        (** the bound on the slowdown factor of
            [early_relation_pin_cpu_clock_no_unknown_query] *)
    early_relation_pin_precheck_no_unknown_query : bool; [@default false]
        (** with [early_pins_no_unknown_query], the early relation pin asks,
            once per piece and before its per-sum shape guesses, whether the
            piece's relaxation with every sequence length in range has a model
            at all; when the answer is [unsat] no guess is asked, since each is
            that question with conjuncts added and would be [unsat] too.  Any
            other answer leaves the guesses as they were.  On a Rust-derived
            input one piece's relaxation is unsatisfiable and its nine
            guesses were a seventh of the pin's time.  Fewer questions with
            the same shapes found, so this never changes an answer; off by
            default *)
    early_relation_pin_full_major_every_no_unknown_query : int option;
        [@default None]
        (** [Some n]: during the early relation pin, the full major collection
            forced before a new Z3 context runs before every n-th one only
            ([Z3interface.with_new_context_full_major_every]), whatever
            [z3_new_context_full_major_every] says elsewhere.  Each shape guess
            and pinned negation is asked in a fresh context, and on a
            Rust-derived input the collections before them were 35-65% of the
            pin's wall time, more under load, the questions themselves being
            small.  Same questions; only the collector's timing changes, and at
            most n dropped contexts wait for it at once *)
    early_pins_full_major_every_no_unknown_query : int option;
        [@default Some 8]
        (** [Some n]: during the whole early-pin stage (sequence-length, point
            and relation pins; [early_pins_no_unknown_query]) the full major
            collection forced before a new Z3 context runs before every n-th
            one only, as [early_relation_pin_full_major_every_no_unknown_query]
            does for the relation pin alone (which, when set, still governs
            that pin).  Same questions; only the collector's timing changes.
            Why: the pins ask many small questions, each in a fresh context,
            under one shared wall-clock budget; on a Rust-derived input refuted
            only by the point pin, its 28 questions took 7.2 s, 3.6 s of it
            the collections, and at a higher load the stage ran out of its
            10 s before the refuting question, so the input went unanswered;
            on a satisfiable Rust-derived filter the relation pin's 9 s were 7 s
            of collections *)
    early_rewritten_max_pieces_no_unknown_query : int option;
        [@default Some 32]
        (** [Some n]: the early rewritten pass
            ([exact_forms_first_no_unknown_query]) leaves a clause that splits
            into more than [n] pieces ([ClausePieces.of_clause], each piece
            counted by its own sub-pieces, the questions the pass would ask) to
            the early sequence instantiation after it, which
            splits it itself, groups pieces that share their premise and asks
            each group once; the pass asks it nothing.  Only which stage asks
            first changes: the pass reads proofs and refutations of exact
            rewrites, which the stages after it ask again when the sequence
            instantiation does not decide the clause.  Why: on a Rust-derived
            loop-body clause of 69 pieces in families of 4-8 that differ only
            in their goal, the pass asked every piece in a fresh context, 18-25
            s of a 120 s budget at a load of 4-8, 27 of the questions left
            undecided in families, while the sequence instantiation proves every
            piece and asks one question per family; [Some 32] by default *)
    early_rewritten_refute_skipped_no_unknown_query : bool; [@default false]
        (** with [early_rewritten_max_pieces_no_unknown_query], a clause the
            early rewritten pass skips for its piece count is still asked once,
            whole, in its rewritten form, at the pass's budget
            ([ClausePieces.early_question]), and only a countermodel is read:
            an invalid clause is refuted there, a valid or undecided one costs
            that one question and is left to the sequence instantiation as
            without the switch.  Why: an invalid clause of more pieces than
            the bound, refuted by the pass in 1.6 s with four questions when
            the pass asked it, was otherwise asked again only by the late
            rewritten pass, which the time limit did not reach; off by
            default *)
    early_rewritten_full_major_every_no_unknown_query : int option;
        [@default Some 8]
        (** [Some n]: during the early rewritten pass
            ([exact_forms_first_no_unknown_query]'s piece-by-piece questions
            before the early sequence instantiation), the full major collection
            forced before a new Z3 context runs before every n-th one only, as
            [early_pins_full_major_every_no_unknown_query] does for the pins.
            Same questions; only the collector's timing changes.  Why: on a
            Rust-derived loop-body clause the pass asks 69 pieces in the
            sequence-axiom form, each in a context of its own with model
            production off, and the collections before them were 5-11 s of the
            pass's 19-32 s on two cores, more under load; off by default *)
    early_relation_pin_length_shapes_no_unknown_query : bool; [@default true]
        (** with [early_pins_no_unknown_query], the EARLY relation pin finds a
            piece's sequence-length shapes from the piece's length-only
            conjuncts ([RelationPin.length_vectors]): at each length sum, the
            vectors those conjuncts leave (at most six) are confirmed one at a
            time by asking whether the relaxation has a model with exactly
            those lengths, every sequence a literal over fresh elements, and
            a sum they leave empty asks nothing; a sum with more candidates is
            asked as before, by one guess per shape with only the sum fixed.
            A confirmation has no length left to choose and is a small
            question, where a per-sum guess at a sum with a model searched
            the lengths too: on a Rust-derived input refuted only by this pin
            (lengths tied by [len x9 = len x3 + len x5] and two equalities,
            so only sums divisible by three have a model), the guess at the
            refuting sum took 0.5-2.6 s of CPU near idle, overran the
            one-second cap under load and so ended that sum's search, and the
            six guesses at the sums with no model were asked anyway.  The
            shapes found are models of the relaxation, as before, and a pin
            reads only a model of a strengthened negation, so this changes
            which questions are asked and when a refutation is reached, never
            an answer.  The late relation pin is unchanged.  On by default *)
    early_relation_pin_first_no_unknown_query : bool; [@default false]
        (** with [early_pins_no_unknown_query], ask the EARLY relation pin
            before the sequence-length and point pins, instead of after them,
            whenever a clause not yet shown valid has a Boolean-valued array
            among its free variables -- the one shape the relation pin acts
            on; otherwise the order is unchanged.  The three early pins share
            [early_pins_budget_no_unknown_query]'s whole budget in order, and
            on a Rust-derived input refuted only by this pin the two before it
            spent 6-10 s of the 10 s under load (sequence-pinned questions
            timing out at the one-second cap, a point pin on a clause with no
            relation), so the relation pin asked two of its five pinned
            negations, and the late relation pin answered near the end of a
            120 s run or not at all.  The budget, its per-question cap and
            the questions each pin asks are as before; each pin reads only a
            model of a strengthened negation, so this changes which pin is
            asked first and when a refutation is reached, never an answer.
            The late pins are unchanged.  Off by default *)
    early_pins_require_applicable_no_unknown_query : bool; [@default true]
        (** with [early_pins_no_unknown_query], each EARLY pin asks only about
            the clauses and pieces its shape admits, decided before any of its
            questions: the sequence-length pin leaves out the clauses a
            question before it has proved valid and, with
            [pin_seq_lengths_from_model_no_unknown_query], those whose
            relaxation it found to have no model ([SeqPin.refute]); the point
            pin skips a piece with a free variable at a sort every value of
            which holds an element of an uninterpreted sort or a sort variable
            ([ScalarPin.opaque_sort]: no closed point exists for it) and, with
            one satisfiability question, a piece whose cheapest relaxation has
            no model; the relation pin skips a clause with no Boolean-valued
            array among its free variables before splitting it, and asks the
            same cheap question of each piece before building its relaxations.
            A skipped clause or piece is one the pin could not have refuted
            (the relaxation is implied by the negation; a point needs a closed
            value of every free variable, and the decoder renders an element of
            an uninterpreted sort as a variable), so this changes which
            questions are asked and when an answer is reached, never an
            answer.  The late pins are unchanged.  Built for Rust-derived
            inputs whose clauses quantify over generic element types, where
            the point pin's guesses were dropped for want of a closed point
            and the length pin's questions carried the clauses already proved;
            on by default *)
    early_pins_after_exact_forms_no_unknown_query : bool; [@default true]
        (** with [early_pins_no_unknown_query] and
            [exact_forms_first_no_unknown_query], ask the early pins AFTER the
            early rewritten pieces and the early sequence instantiation
            instead of before them ([NoUnknownLadder.early_order]); the early
            pins then also skip every clause those stages showed valid.  Each
            of the two stages is sound alone (the pins read only a
            refutation, the exact forms a refutation of an exact rewrite or a
            proof), so the order changes which questions are asked before an
            answer and when it is reached, never which answer is right: a
            problem the exact forms prove no longer pays the pins' questions,
            and a refutation by a pin is reached later by the time the exact
            forms spend.  Its budget, [early_pins_budget_no_unknown_query],
            starts when the pins start.  Read from traces of 13 Rust-derived
            inputs with no predicate variable left: the early pins took
            8.7-13 s on every input and found nothing on any of them, and the
            three inputs that answer near the 120 s budget are proved by the
            exact forms after them.  Off by default: to be measured *)
    early_pins_raced_no_unknown_query : bool; [@default false]
        (** with [early_pins_after_exact_forms_no_unknown_query] (and
            [early_pins_no_unknown_query]), start the early pins, before the
            exact forms, in a forked copy of the process
            ([PCSatCommon.ParallelRace]) that answers only with a refutation,
            while the process goes on with the exact forms and the rest of the
            ladder in the pins-after order unchanged (its own early pins
            included, after the exact forms).  A copy whose pins
            find a countermodel takes the run over and answers [unsat] from
            it, exactly as the sequential pins would have at that point; a
            copy that finds nothing leaves silently (in the copy each pin has
            the stage's whole budget to itself, a copy delaying nothing); the
            process kills the
            copy when its ladder has a verdict (or raises) and before that
            verdict leaves the ladder.  Sequential, in the pins-after order,
            when no copy can be forked or inside a solve bounded by a
            deadline.  Each side is sound alone (the pins read only a model of
            a strengthened negation; the exact forms read a proof or a
            refutation of an exact rewrite), so the race changes when an
            answer is reached, never which.  Why: the pins-after order spares
            a problem the exact forms prove the pins' questions, which on the
            satisfiable twin of a Thrust pair spend their whole budget, and
            makes the unsatisfiable twin, which the sequence-length pin
            refutes in one to six seconds, wait a minute or more for the exact
            forms to stay undecided; no shape test tells the two apart (the
            twins share their shape), and a second core does not have to.
            Off by default, a candidate for the next default-deciding batch:
            three runs each against the default on eight Rust-derived inputs
            gave a refutation at 14-17 s where the default took 77-92 s and at
            80-119 s where it took 191-241 s, and the six others answered
            alike *)
    early_point_pin_first_no_unknown_query : bool; [@default true]
        (** with [early_pins_after_exact_forms_no_unknown_query] (and
            [early_pins_no_unknown_query], [pin_scalars_no_unknown_query]),
            ask the point pin alone BEFORE the exact forms
            ([NoUnknownLadder.Point_pin]), under a budget of its own equal to
            [early_pins_budget_no_unknown_query] and started when it starts,
            and the other early pins after the exact forms as before.  The
            later early pins leave the point pin out when the first one
            searched every open clause under full per-question caps
            ([NoUnknownLadder.point_pin_searched_all]); the late pins at the
            end of the ladder are unchanged.  The point pin reads only a
            point at which a clause's negation is proved valid (a
            countermodel), so this changes when a refutation is reached and
            which questions are asked before it, never an answer.
            Why the point pin and no other: its first questions are about
            quantifier-free relaxations and its proofs about the clause with
            every free variable fixed to a closed value, where the
            sequence-length pin's pinned negations keep their quantifiers and
            on an input with no countermodel run to their per-question cap
            (the cost the pins-after order saves).  Two Rust-derived
            refutations the pins-after order delayed are both found by the
            point pin: one in about a second after the quick sweep, but only
            after a minute of exact forms; the other after the
            sequence-length pin, which with every clause still open spent the
            pins' shared budget and left the point pin about two seconds.
            On by default: five runs each against the default on those two
            inputs gave the refutation within 12-17 s (default none in 30 s)
            and 64-101 s (default none in 120 s), and an input decided by the
            CEGIS loop answered alike *)
    early_cheap_pins_first_no_unknown_query : bool; [@default false]
        (** with [early_pins_after_exact_forms_no_unknown_query] (and
            [early_pins_no_unknown_query]), ask BEFORE the exact forms the one
            pin question whose cost the problem's shape bounds
            ([SeqPin.cheap_first]; [NoUnknownLadder.Cheap_pins]): the negation
            of the clauses not yet shown valid with every free sequence pinned
            to the empty sequence, asked only when some such clause has a free
            sequence, does not simplify to [false] there, and the simplified
            question has at most [SeqPin.cheap_max_size] nodes.  It is asked
            once, under the early pins' per-question cap; a model is a
            refutation (the question is a strengthening of the negation),
            anything else is dropped and the ladder goes on exactly as without
            the switch, the full early pins still asked after the exact forms.
            So it changes when a refutation is reached and costs at most one
            question when the shape is wrong, never an answer.  Built for an
            input the pins-after order slowed from a refutation in the first
            seconds (by this very question) to one after a minute of the
            sequence instantiation.  Off by default: to be measured *)
    conj_timeout_after_early_no_unknown_query : int option; [@default None]
        (** [Some ms]: once the early rewritten pieces and the early sequence
            instantiation ([exact_forms_first_no_unknown_query]) have run and
            left the problem undecided, the whole-conjunction questions (the
            conjunction, the conjunction with its single-constructor binders
            opened, and the conjunction of the rewritten clauses not yet shown
            valid) are asked with at most [ms] milliseconds each instead of
            [no_unknown_query_timeout], and [ms <= 0] does not ask them
            ([NoUnknownLadder.conj_timeout], [NoUnknownLadder.ask_conj]).  The
            per-clause and per-piece questions keep their budget.  Only
            [`Valid] and [`Invalid] are read from these questions, so a
            shorter budget can only lose an answer one of them would have
            given between [ms] and the full budget, to the later stages, and
            changes which questions are asked after it.  Read from the same
            traces: the conjunction and its opened form each spent their full
            10 s (11.9-13.4 s of wall time) on two inputs and decided nothing
            on any of the 13.  [None], the default, keeps the full budget *)
    pin_scalars_default_compound_values : bool; [@default false]
        (** in the point pin, give a variable the guessed model leaves
            unassigned a closed default value also when its sort is a tuple or
            a datatype (the constructor of fewest arguments applied to
            defaults, recursively), where without it the point is dropped;
            the point is still proved by the validity of the pinned negation,
            so a default costs time and never an answer *)
    split_clause_heads_no_unknown_query : bool; [@default true]
        (** when preprocessing leaves no predicate variable and a residual
            clause is asked alone, first ask each of its [ClausePieces] -- a
            clause [body => c1 /\ ... /\ cn] is valid exactly when every
            [body => ci] is -- and ask the whole clause only when a piece is
            undecided ([ClausePieces.ask_by_pieces]); when off, each clause is asked
            whole, as before.  On by default: on the 112-file control it moved
            no verdict *)
    uncapped_conjunction_pieces_no_unknown_query : bool; [@default true]
        (** in the sequence instantiation of the zero-unknown verdict, split a
            conjunction into its sides' pieces however many they are together
            ([SeqInstantiation.uncapped_conjunction_pieces]), instead of
            keeping it whole once they pass the bound that limits a
            disjunction's distribution, and split a disjunction past that
            bound along one side as [pointwise_concat_candidates_no_unknown_query]
            does, so that no clause gets fewer pieces than without it.  Exact:
            a conjunction is valid exactly when each of its pieces is, so only
            which questions are asked changes.  Why: one more conjunct in a
            loop-body clause's conclusion took its 42 + 32 goal pieces past the
            bound, and the whole conclusion became one question whose
            instantiated form was millions of nodes and left undecided, where
            each piece is proved in a fraction of a second.  On by default *)
    group_open_pieces_no_unknown_query : bool; [@default true]
        (** with [group_piece_forms_no_unknown_query], let a piece join any
            open group whose common part admits it, not only the group of
            the pieces just before it ([SeqInstantiation.group_open_pieces]),
            and ask the groups once every piece has its first form.  Sound as
            the grouping is: a group's question implies each member's first
            form.  Why: a loop-body clause's pieces fall into a few families
            with different premise instances, interleaved, so grouping only
            consecutive pieces asked 18 questions where 3 would do *)
    lead_forms_before_grouping_no_unknown_query : bool; [@default true]
        (** with [group_piece_forms_no_unknown_query] (consecutive grouping;
            open grouping only with
            [lead_forms_under_open_grouping_no_unknown_query]), ask each
            piece's forms that come before its deep forms (the
            push-witness and matched-instance forms) before building the deep
            first form the grouping compares, and leave a piece they prove out
            of every group ([SeqInstantiation.lead_forms_before_grouping]); a
            piece they do not prove is grouped as before and asked its
            remaining forms, so no question is asked twice.  Sound: only a
            proof of a form, which is a strengthening of its piece, is read.
            Why: on a Rust-derived loop clause the deep first forms, about a
            second each at idle, were built for twelve pieces of which the
            matched-instance forms then proved eleven at 0.1-0.2 s each *)
    lead_forms_under_open_grouping_no_unknown_query : bool; [@default false]
        (** let [lead_forms_before_grouping_no_unknown_query] act under
            [group_open_pieces_no_unknown_query] too: each piece's lead forms
            are asked before it is listed for open grouping, a piece they
            prove joins no group, and a member asked alone after its group's
            question fails starts after the lead forms already asked
            ([SeqInstantiation.lead_forms_under_open_grouping]).  Off, the
            open path asks no lead stage before grouping.  Needs
            [lead_forms_before_grouping_no_unknown_query]; ignored while
            [lead_forms_for_unasked_groups_no_unknown_query] is set, which
            decides the open path's lead forms alone.  Sound: only a proof of
            a form is read, and no question is asked twice.  Why off: on one
            Rust-derived counter clause it proved six pieces whose grouped
            question ran to the cap, while on a Rust-derived map clause its
            lead proofs displaced cheaper grouped questions and the file, at
            the edge of its budget, lost answers *)
    lead_forms_for_unasked_groups_no_unknown_query : bool; [@default true]
        (** with [group_open_pieces_no_unknown_query], ask a piece's lead
            forms (push-witness and matched-instance forms) as a stage of
            their own, before its other forms, only for the pieces no grouped
            question is asked about -- members of a group whose question is
            past [group_question_max_nodes_no_unknown_query], a group of one,
            a piece with no first form -- and list every piece for grouping
            as with [lead_forms_before_grouping_no_unknown_query] off, which
            then does not act on the open path (nor does
            [lead_forms_under_open_grouping_no_unknown_query]; this switch
            acts whether or not that one is set)
            ([SeqInstantiation.lead_forms_for_unasked_groups]).  The pieces
            affected are asked the same forms in the same order; only the
            lemma route's one attempt after a form's timeout
            ([lemma_application_after_form_timeout_no_unknown_query]) moves
            after the lead forms.  Sound: only a proof of a form, which
            implies its piece, is read.  Why: on a Rust-derived counter
            clause a skipped five-piece question and a piece alone each left
            a piece whose matched-instance form timed out to the lemma route,
            which ran 60 s without a proof where the piece's next
            matched-instance form proved it, while asking every piece's lead
            forms before grouping displaced cheap grouped proofs on another
            clause *)
    lead_forms_under_open_grouping_min_nodes_no_unknown_query : int option;
        [@default None]
        (** with [group_open_pieces_no_unknown_query], a group of two or more
            pieces whose grouped question has more than this many nodes is
            not asked; its members are asked their lead forms (push-witness
            and matched-instance forms) as a stage of their own, before their
            other forms.  Every other group is asked as with the switch off,
            and no lead stage is asked before grouping on the open path
            ([lead_forms_under_open_grouping_no_unknown_query] is not read
            while this is set) ([SeqInstantiation.lead_forms_open_min_nodes]).
            Sound: only a proof of a form, which implies its piece, is read,
            and no question is asked twice.  Why: the lead stage before
            grouping proved six pieces of a Rust-derived counter clause whose
            grouped question of about 428,000 nodes proved nothing in about
            90 s, while on a Rust-derived bit-set clause it replaced two
            small grouped questions proving 128 pieces by 129 serial
            questions; the size of the grouped question tells the two
            apart *)
    replay_piece_fresh_names_no_unknown_query : bool; [@default true]
        (** in the sequence instantiation of the zero-unknown verdict, build
            the first forms of a clause's pieces for grouping with the fresh
            names replayed from one scope per clause
            ([SeqInstantiation.replay_piece_names]), so the instances of the
            premise the pieces share are named alike in every piece.  Sound:
            each first form is the strengthening of its piece it always is,
            only named differently, and the grouped question still implies
            each member's form, whatever names two members share.  Why: each
            piece's first form drew hundreds of fresh names of its own, which
            the grouping renamed back into one before seeing the common part *)
    clause_piece_bound_no_unknown_query : int option; [@default Some 4]
        (** with [Some m], a residual clause asked by its [ClausePieces] in
            the zero-unknown verdict is split into at most [m] pieces rather
            than the default bound's, and a piece left undecided is split once
            more, down to the default bound ([ClausePieces.ask_by_pieces]);
            [None], or a bound not below the default, keeps the default split.
            Each split is exact, so the bound changes which questions are
            asked and their number, never what an answer means.  The quick
            sweep keeps the default split *)
    seq_as_array_no_unknown_query : bool; [@default false]
        (** when preprocessing leaves no predicate variable, ask each validity
            question whose sequences are concat-free and whose reads are
            range-guarded as arrays plus a length first
            ([Z3interface.check_valid_seq_as_array], an equisatisfiable
            translation), and untranslated when that is undecided or the
            question is outside the fragment; when off, the questions are asked
            as they are *)
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
   [phase] ([ladder_stage_rlimits_no_unknown_query]): the first binding of
   [phase] in [stage_rlimits] when there is one, else [default] (the
   ladder-wide [no_unknown_query_rlimit]).  Total; [stage_rlimits = []] gives
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
   ([ladder_seq_axiom_rlimit_no_unknown_query]): [with_ (Some (units,
   kill_ms)) f] runs [f] with the fallback's questions under [units] and its
   wall-clock budget replaced by [kill_ms] (each question's own budget still
   capping it); [with_ None f] is [f ()].  Both settings are per domain and
   restored on return and on raise.  Only an undecided answer is ever turned
   into a proof by the fallback, so the pair changes which undecided
   questions are proved, never what a proof says. *)
module LadderSeqAxiomRlimit = struct
  let with_ pair f =
    match pair with
    | None -> f ()
    | Some (units, kill_ms) ->
        Z3Smt.Z3interface.with_seq_axiom_rlimit (Some units) @@ fun () ->
        Z3Smt.Z3interface.with_seq_axiom_fallback_base (Some kill_ms) f

  (* Which fallbacks get the pair, and with which count
     ([ladder_seq_axiom_rlimit_refused_only_no_unknown_query],
     [ladder_seq_axiom_units_per_node_no_unknown_query]).

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

(* The sweep of unknown-free clauses ([sweep_unknown_free_clauses]); the
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
     configuration's [*_no_unknown_query] fields; returns whether the
     contextual rule is applied in place and whether as an extra form, which
     are never both.  Each switch adds an equivalence to the rewrite, so it
     changes which questions a solver can answer, never what an answer
     means.  The head of this module says who calls it. *)
  let set_onepoint_rewrite_switches (config : Config.t) =
    Ast.Evaluator.split_constructor_equations :=
      config.split_constructor_equations_no_unknown_query;
    Ast.Evaluator.onepoint_array_reads :=
      config.onepoint_array_reads_no_unknown_query;
    let contextual_in_place =
      config.contextual_ite_no_unknown_query
      && not config.contextual_ite_as_extra_form_no_unknown_query
    in
    let contextual_extra =
      config.contextual_ite_no_unknown_query
      && config.contextual_ite_as_extra_form_no_unknown_query
    in
    Ast.Evaluator.contextual_ite := contextual_in_place;
    SeqInstantiation.contextual_ite_extra_form := contextual_extra;
    Ast.Evaluator.surjective_pairing :=
      config.surjective_pairing_no_unknown_query;
    Ast.Evaluator.surjective_pairing_nested :=
      config.surjective_pairing_nested_no_unknown_query;
    Ast.Evaluator.lift_spine_blocks := config.lift_spine_blocks_no_unknown_query;
    (contextual_in_place, contextual_extra)

  (* The process-wide switches of [SeqInstantiation]'s witness instantiation,
     set from the configuration's [*_no_unknown_query] fields; [print]
     traces the cvc5 retry of an undecided piece.  Setting a switch changes
     which instantiated forms are built, never what a proof of one means. *)
  let set_seq_instantiation_switches ?(print = fun (_ : string lazy_t) -> ())
      (config : Config.t) =
    (* with the ladder's integer-binder split on and [verbose], one stderr
       line at exit tallying the questions it rewrote: a diagnostic, so a
       plain run's output stays the answer *)
    if config.split_int_binders_at_ite_no_unknown_query && config.verbose then
      Ast.IntBinderSplit.report_tallies ();
    SeqInstantiation.onepoint_split_forms :=
      config.onepoint_split_no_unknown_query;
    SeqInstantiation.instantiate_element_binders :=
      config.instantiate_element_binders_no_unknown_query;
    SeqInstantiation.seq_array_view_candidates :=
      config.seq_array_view_candidates_no_unknown_query;
    SeqInstantiation.pointwise_array_witnesses :=
      config.pointwise_array_witnesses_no_unknown_query;
    SeqInstantiation.witness_forms :=
      config.witness_forms_no_unknown_query;
    SeqInstantiation.drop_array_hypotheses :=
      config.drop_array_hypotheses_no_unknown_query;
    SeqInstantiation.skolemize_positive_universals_before_instantiation
    := config.skolemize_positive_universals_no_unknown_query;
    SeqInstantiation.cancel_forced_sequence_binders_before_instantiation
    := config.cancel_forced_sequence_binders_no_unknown_query;
    SeqInstantiation.offset_int_candidates
    := config.offset_int_candidates_no_unknown_query;
    SeqInstantiation.array_read_int_candidates
    := config.array_read_int_candidates_no_unknown_query;
    SeqInstantiation.index_map_shift_candidates
    := config.index_map_shift_candidates_no_unknown_query;
    SeqInstantiation.index_map_join_candidates
    := config.index_map_join_candidates_no_unknown_query;
    SeqInstantiation.literal_range_int_candidates
    := config.literal_range_int_candidates_no_unknown_query;
    SeqInstantiation.nested_focus_forms
    := config.nested_focus_forms_no_unknown_query;
    SeqInstantiation.element_candidates_through_constructors
    := config.element_candidates_through_constructors_no_unknown_query;
    SeqInstantiation.bool_binder_candidates
    := config.bool_binder_candidates_no_unknown_query;
    SeqInstantiation.split_seq_prefix_over_concat
    := config.split_seq_prefix_over_concat_no_unknown_query;
    SeqInstantiation.split_seq_prefix_focus_only
    := config.split_seq_prefix_focus_only_no_unknown_query;
    SeqInstantiation.offset_int_candidates_chain_only
    := config.offset_int_candidates_chain_only_no_unknown_query;
    SeqInstantiation.chain_candidates_free_only
    := config.chain_candidates_free_only_no_unknown_query;
    SeqInstantiation.chain_concat_candidates
    := config.chain_concat_candidates_no_unknown_query;
    SeqInstantiation.chain_focus_forms
    := config.chain_focus_form_no_unknown_query;
    SeqInstantiation.chain_focus_push_witnesses
    := config.chain_focus_push_witnesses_no_unknown_query;
    SeqInstantiation.case_split_index_forms
    := config.case_split_index_forms_no_unknown_query;
    (* set only around the coordinator's own sequence instantiation, where
       its short-budget asker exists *)
    SeqInstantiation.index_case_ask := None;
    SeqInstantiation.index_case_max_size_ratio
    := config.case_split_index_max_size_ratio_no_unknown_query;
    SeqInstantiation.lazy_plain_form
    := config.lazy_plain_form_no_unknown_query;
    SeqInstantiation.matched_instance_forms
    := config.matched_instance_forms_no_unknown_query;
    SeqInstantiation.matched_instance_hyp_budget
    := config.matched_instance_hyp_budget_no_unknown_query;
    SeqInstantiation.matched_instance_aligned_hyps
    := config.matched_instance_aligned_hyps_no_unknown_query;
    SeqInstantiation.matched_instance_element_candidates
    := config.matched_instance_element_candidates_no_unknown_query;
    SeqInstantiation.matched_instance_chain_join_candidates
    := config.matched_instance_chain_join_candidates_no_unknown_query;
    SeqInstantiation.chain_join_direct_reads
    := config.chain_join_direct_reads_no_unknown_query;
    SeqInstantiation.matched_instance_last_index_candidates
    := config.matched_instance_last_index_candidates_no_unknown_query;
    SeqInstantiation.matched_instance_collections_only
    := config.matched_instance_collections_only_no_unknown_query;
    SeqInstantiation.chain_join_focused
    := config.chain_join_focused_no_unknown_query;
    SeqInstantiation.assoc_concat_matching
    := config.matched_instance_assoc_open_no_unknown_query;
    SeqInstantiation.open_scalar_matches
    := config.matched_instance_assoc_open_no_unknown_query;
    SeqInstantiation.max_matched_form_size
    := config.max_matched_form_size_no_unknown_query;
    SeqInstantiation.max_chain_join_focus_size
    := config.max_chain_join_focus_size_no_unknown_query;
    SeqInstantiation.ground_funapps_linear
    := config.ground_funapps_linear_no_unknown_query;
    SeqInstantiation.matched_bound_before_ranking
    := config.matched_bound_before_ranking_no_unknown_query;
    SeqInstantiation.piece_max_nodes
    := config.seqinst_max_nodes_no_unknown_query;
    SeqInstantiation.piece_max_int_input_nodes
    := config.seqinst_max_int_input_nodes_no_unknown_query;
    SeqInstantiation.chain_assoc_match_forms
    := config.chain_assoc_match_no_unknown_query;
    SeqInstantiation.prepend_unit_candidates
    := config.prepend_unit_candidates_no_unknown_query;
    SeqInstantiation.pointwise_concat_candidates
    := config.pointwise_concat_candidates_no_unknown_query;
    SeqInstantiation.uncapped_conjunction_pieces
    := config.uncapped_conjunction_pieces_no_unknown_query;
    SeqInstantiation.share_premise_instances
    := config.share_premise_instances_no_unknown_query;
    SeqInstantiation.replay_piece_names
    := config.replay_piece_fresh_names_no_unknown_query;
    SeqInstantiation.group_open_pieces
    := config.group_open_pieces_no_unknown_query;
    SeqInstantiation.group_piece_forms
    := config.group_piece_forms_no_unknown_query;
    SeqInstantiation.lead_forms_before_grouping
    := config.lead_forms_before_grouping_no_unknown_query;
    SeqInstantiation.lead_forms_under_open_grouping
    := config.lead_forms_under_open_grouping_no_unknown_query;
    SeqInstantiation.lead_forms_for_unasked_groups
    := config.lead_forms_for_unasked_groups_no_unknown_query;
    SeqInstantiation.lead_forms_open_min_nodes
    := config.lead_forms_under_open_grouping_min_nodes_no_unknown_query;
    SeqInstantiation.share_piece_simplify
    := config.share_piece_simplify_no_unknown_query;
    SeqInstantiation.share_replayed_int_instances
    := config.share_replayed_int_instances_no_unknown_query;
    SeqInstantiation.share_deep_shapes
    := config.share_deep_shapes_no_unknown_query;
    SeqInstantiation.group_question_max_nodes
    := config.group_question_max_nodes_no_unknown_query;
    PCSatCommon.LemmaApplication.extended
    := config.lemma_application_extended_no_unknown_query;
    PCSatCommon.LemmaApplication.goal_first_probe
    := config.lemma_goal_first_probe_no_unknown_query;
    SeqInstantiation.lemma_before_retry
    := config.lemma_application_before_cvc5_no_unknown_query;
    SeqInstantiation.lemma_after_form_timeout
    := config.lemma_application_after_form_timeout_no_unknown_query;
    SeqInstantiation.lemma_application_prover
    := Option.map config.lemma_application_ms_no_unknown_query ~f:(fun ms piece ->
           (* at most the budget left to a caller that set one
              ([SeqInstantiation.with_last_attempt_budget]) *)
           match SeqInstantiation.last_attempt_ms ms with
           | None -> false
           | Some ms ->
           Common.PhaseTime.with_phase "lemma-application" (fun () ->
               let outcome =
                 PCSatCommon.LemmaApplication.z3_outcome ~ms
                   ?rlimits:config.lemma_application_rlimits_no_unknown_query
               in
               PCSatCommon.LemmaApplication.prove ~outcome
                 ~trace:(fun r -> print @@ lazy ("[no-unknown verdict] " ^ Lazy.force r))
                 ~usable:(fun fact -> not (Z3Smt.Z3interface.may_not_return fact))
                 ~valid:(fun psi ->
                   match outcome psi with `Valid -> true | _ -> false)
                 piece));
    SeqInstantiation.true_forms_proved
    := config.ladder_proof_shortcuts_no_unknown_query;
    PCSatCommon.Cvc5Proof.shortcuts
    := config.ladder_proof_shortcuts_no_unknown_query;
    SeqInstantiation.undecided_piece_prover
    := Option.map config.ladder_cvc5_retry_ms_no_unknown_query ~f:(fun ms phi ->
           (* the piece as the ladder's Z3 checks ask it: where
              [Z3interface.with_split_int_binders] is in force in this domain
              ([split_int_binders_at_ite_no_unknown_query]), its integer
              binders are split at their [ite] thresholds and the upper parts
              shifted to start at zero, and otherwise it is [phi] itself.  The
              rewrite is an equivalence in every model that adds no free
              variable, so cvc5's proof of it is a proof of [phi] *)
           match SeqInstantiation.last_attempt_ms ms with
           | None -> false
           | Some ms ->
           let phi = Z3Smt.Z3interface.split_int_binders_here phi in
           (* timed as its own phase: the retry runs cvc5 in a separate
              process, so its wait is otherwise charged to no named phase *)
           Common.PhaseTime.with_phase "cvc5-retry" (fun () ->
               PCSatCommon.Cvc5Proof.valid_within
                 ~trace:(fun r ->
                   print @@ lazy ("[no-unknown verdict] cvc5 retry: " ^ r))
                 ?rlimit:config.ladder_cvc5_rlimit_no_unknown_query ~ms
                 ~id:None
                 (Z3Smt.Z3interface.fenv_reached_by (Ast.LogicOld.get_fenv ())
                    phi)
                 phi))

  (* both setters, for a reader that does not need the contextual-ite pair *)
  let set ?print (config : Config.t) =
    ignore (set_onepoint_rewrite_switches config : bool * bool);
    set_seq_instantiation_switches ?print config
end

module type CoordinatorType = sig
  val solve :
    ?witness:WitnessConfig.t ->
    ?oracle:PCSP.Problem.oracle ->
    PCSP.Problem.t ->
    State.output Or_error.t
end

(* raised by the zero-unknown verdict's ladder when
   [zero_unknown_reads_strict_deadline] is on and a strict solve deadline has
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

  (* the grouping counters of [group_piece_forms_no_unknown_query], on stderr
     whenever that switch is on, so that a run shows that it was read and what
     the grouped questions did, without the verbose trace (which prints every
     form asked, megabytes each on the inputs the switch is for) *)
  module GroupDebug =
    Common.Debug.Make
      ((val Common.Debug.Config.(
              if config.group_piece_forms_no_unknown_query then enable
              else disable)))

  let set_onepoint_rewrite_switches () =
    LadderSwitches.set_onepoint_rewrite_switches config

  let set_seq_instantiation_switches () =
    LadderSwitches.set_seq_instantiation_switches ~print:Debug.print config

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
           the relation), which a template under [related_position_quals]
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
        let unsat_witness =
          Option.bind !last_version_space ~f:(fun vs ->
              Option.map !(vs.VersionSpace.unsat_witness) ~f:(fun w ->
                  { w with UnsatWitness.problem = Some pcsp }))
        in
        Option.iter unsat_witness ~f:(fun w ->
            Debug.print @@ lazy (UnsatWitness.str_of w);
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
    fun senv phi -> Z3interface.check_sat [ phi ] senv (Z3.mk_context [])

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
       formula) and [P] may not occur in a pure part of any clause.  For
       [Tot] both are checked below; for FN only the second is, and only
       against the clauses outside the eliminated shape.
     The quantifier eliminations and simplifications applied to [body] are
     equivalences, and a [None] from either theory's reader or an undecided
     game keeps the clauses for the loop, which is only incompleteness. *)
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
    let tot_blocked =
      (* the two conditions the [Tot] refutation needs that [pvs2] does not
         give (see above): [P] in a pure part of a clause of the eliminated
         shape, and a clause of [P] whose pure part mentions an unknown *)
      Set.Poly.union_list
      @@ List.map (Set.to_list cls1) ~f:(fun ((_, _, _, phi) as cl) ->
          let in_phi = Set.inter (Ast.Logic.Term.fvs_of phi) unknowns in
          if Set.is_empty in_phi then in_phi
          else Set.union in_phi (Ast.Clause.pvs_of cl))
    in
    let cls11, cls12 =
      Set.partition_tf cls1 ~f:(fun cl ->
          let p = Set.choose_exn @@ Ast.Clause.pvs_of cl in
          (not @@ Set.mem pvs2 p)
          && not (PCSP.Problem.is_tot_pred pcsp p && Set.mem tot_blocked p))
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
              else Kind.tot_positions_of @@ PCSP.Problem.kind_of pcsp tvar
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
                  | Failure msg
                    when String.is_prefix msg
                           ~prefix:"[z3:term_of] unsupported Z3 operator" ->
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
                              (Logic.Term.mk_var x) t)) )))
    in
    let pvs1 = Set.Poly.of_list @@ List.map ~f:fst sol_eliminated in
    let params = PCSP.Problem.params_of pcsp in
    let params =
      {
        params with
        senv = Map.Poly.filter_keys params.senv ~f:(Set.mem pvs1 >> not);
        kind_map = Map.Poly.filter_keys params.kind_map ~f:(Set.mem pvs1 >> not);
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

  (* [prove_unknown_free_clauses_first].  Contract: [`Rest p] is either [pcsp]
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
    if (not config.prove_unknown_free_clauses_first) || Map.Poly.is_empty senv
    then `Rest pcsp
    else
      match PCSP.Problem.clauses_of_opt ~full_clauses:false pcsp with
      | None -> `Rest pcsp
      | Some cnf -> (
          let params = PCSP.Problem.params_of pcsp in
          let is_free = UnknownFreeSweep.unknown_free senv in
          let free =
            Set.filter (PCSP.Problem.clauses_of pcsp) ~f:is_free
          in
          if Set.is_empty free then `Rest pcsp
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
                match config.prove_unknown_free_clauses_first_budget_ms with
                | Some ms when config.prove_unknown_free_clauses_first_within_deadline
                  -> (
                    match PCSatCommon.SolveDeadline.remaining_ms () with
                    | Some r -> Some (Int.min ms r)
                    | None -> Some ms)
                | b -> b
              in
              match budget_ms with
              | None -> in_process ()
              | Some _
                when config.prove_unknown_free_clauses_first_within_deadline
                     && PCSatCommon.SolveDeadline.expired () ->
                  Ok
                    ( PCSP.Problem.Unknown,
                      {
                        State.num_cegis_iters = 0;
                        unsat_witness = None;
                        kind_certificates = Map.Poly.empty;
                      } )
              | Some ms
                when config.prove_unknown_free_clauses_first_in_process_when_large
                     && not
                          (Common.ForkGuard.fork_fits
                             ~heap_bytes:(Common.ForkGuard.major_heap_bytes ())
                             ~headroom:(Common.ForkGuard.cgroup_headroom_bytes ()))
                ->
                  (* too large to copy: in this process, under the same
                     budget, as a strict deadline *)
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
                        PCSatCommon.ForkedQuery.run ~ms (fun () ->
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
                      if witness.WitnessConfig.unsat then (
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
    let if_witness w = if witness.WitnessConfig.unsat then Some w else None in
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
            if not config.zero_unknown_reads_strict_deadline then body ()
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
            config.arith_solver_no_unknown_query
          @@ fun () ->
          Z3Smt.Z3interface.with_split_int_binders
            config.split_int_binders_at_ite_no_unknown_query
          @@ fun () ->
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
          let prepare phi =
            let phi =
              if config.subst_projection_definitions_no_unknown_query then
                Ast.Evaluator.subst_seq_projection_definitions phi
              else phi
            in
            let phi = Ast.Evaluator.split_seq_reads_for_validity phi in
            if
              config.split_seq_prefix_over_concat_no_unknown_query
              && not config.split_seq_prefix_focus_only_no_unknown_query
            then
              Ast.Evaluator.rewrite_seq_prefix_over_concat phi
            else phi
          in
          let per_clause =
            List.map ~f:prepare @@ Set.to_list @@ Ast.ClauseSetOld.to_formulas
            @@ Ast.ClauseSet.to_old_clause_set Map.Poly.empty
            @@ PCSP.Problem.clauses_of pcsp
          in
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
            if config.onepoint_split_no_unknown_query then
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
             [seq_axioms_first_fresh_no_unknown_query]; see [AxiomsFirst.ask]
             for the order and why it changes only timing *)
          let axioms_first ?(enabled = true) phi k =
            match config.seq_axioms_first_no_unknown_query with
            | Some ms ->
                AxiomsFirst.ask ~enabled
                  ~applies:Z3Smt.SeqAxiomEncoding.mentions_seq
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
             report at the end (see [report_budget_exhaustion]); every query
             goes through [budgeted], which also applies the rlimit *)
          let budget_cut = ref 0 in
          let budget_asked = ref 0 in
          (* LADDER-PROFILE tracing: which stage of the ladder a question
             belongs to, printed with each question and at each transition *)
          let ladder_phase = ref "start" in
          let ladder_t0 = Common.Clock.now_s () in
          let ladder_stage, _ = Common.PhaseTime.stages () in
          let deadline_passed () =
            config.zero_unknown_reads_strict_deadline
            && PCSatCommon.SolveDeadline.expired_strict ()
          in
          let enter_phase name =
            if deadline_passed () then raise Zero_unknown_deadline_passed;
            ladder_stage name;
            ladder_phase := name;
            Debug.print
            @@ lazy
                 (sprintf "[no-unknown verdict] phase %s at %.2f s" name
                    (Common.Clock.now_s () -. ladder_t0))
          in
          let stage_rlimit =
            LadderStageRlimit.find
              ~stage_rlimits:config.ladder_stage_rlimits_no_unknown_query
              ~default:config.no_unknown_query_rlimit
          in
          let budgeted f =
            let started = Common.Clock.now_s () in
            let r =
              (* past a strict deadline the question is not asked; it is
                 reported as one that ran out of its budget, which every
                 caller reads as undecided *)
              if deadline_passed () then `Timeout
              else
                (* with [ladder_seq_axiom_rlimit_no_unknown_query], the
                   fallback is bounded by its count and killed at its own
                   wall clock; the lemma route sets its own pair inside; with
                   either refinement of the pair, it is chosen per fresh
                   question in [fresh_body] instead *)
                LadderSeqAxiomRlimit.with_
                  (LadderSeqAxiomRlimit.around_question
                     ~refused_only:
                       config.ladder_seq_axiom_rlimit_refused_only_no_unknown_query
                     ~per_node:config.ladder_seq_axiom_units_per_node_no_unknown_query
                     config.ladder_seq_axiom_rlimit_no_unknown_query)
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
          (* [pointwise_array_countermodels_no_unknown_query]: an undecided
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
            | _ when not config.pointwise_array_countermodels_no_unknown_query
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
          let ask_within timeout phi =
            note_asking ~kind:"pooled" timeout phi;
            budgeted @@ fun () ->
            pointwise_refute ~timeout phi
            @@ axioms_first phi @@ fun phi ->
            (if config.seq_as_array_no_unknown_query then
               Z3Smt.Z3interface.check_valid_seq_as_array
             else Z3Smt.Z3interface.check_valid)
              ~timeout:(Some timeout)
              ~fresh_solver:false ~id:None
              (Ast.LogicOld.get_fenv ()) phi
          in
          let ask = ask_within config.no_unknown_query_timeout in
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
          (* [implied_factor_equalities_no_unknown_query]: the question with
             the factor equations its linear facts imply stated, an
             equivalence ([Z3interface.implied_factor_equalities]); [phi]
             itself when off *)
          let factor_eqs ~timeout phi =
            if not config.implied_factor_equalities_no_unknown_query then phi
            else
              Common.PhaseTime.with_phase "factor-eqs" (fun () ->
                  Z3Smt.Z3interface.implied_factor_equalities ~timeout ~id:None
                    (Ast.LogicOld.get_fenv ()) phi)
          in
          (* [native] asks the solver itself ([native_check] in-process, or a
             forked copy of it) *)
          let native_check ~timeout phi =
            let open Ast.LogicOld in
            let phi = factor_eqs ~timeout:(Option.value timeout ~default:10000) phi in
            match
              (if config.seq_as_array_no_unknown_query then
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
          (* [weaken_refused_questions_no_unknown_query]: a refused question
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
            match config.weaken_refused_questions_no_unknown_query with
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
          let fresh_body ?(native = native_check) timeout phi =
            let open Ast.LogicOld in
            pointwise_refute ~timeout phi
            @@ axioms_first ~enabled:config.seq_axioms_first_fresh_no_unknown_query
              phi
            @@ fun phi ->
            let refused = Z3Smt.Z3interface.may_not_return phi in
            (* the fallback's own count, when the pair is chosen per question
               ([LadderSeqAxiomRlimit.for_fallback]); the solver was not asked
               a refused question unless a forked copy asked it *)
            let fallback_pair =
              LadderSeqAxiomRlimit.for_fallback
                ~refused_only:
                  config.ladder_seq_axiom_rlimit_refused_only_no_unknown_query
                ~per_node:config.ladder_seq_axiom_units_per_node_no_unknown_query
                ~only_attempt:
                  (refused
                  && Option.is_none
                       config.fork_refused_questions_no_unknown_query)
                ~size:
                  (match
                     config.ladder_seq_axiom_units_per_node_no_unknown_query
                   with
                  | None -> 0
                  | Some _ -> Formula.ast_size phi)
                config.ladder_seq_axiom_rlimit_no_unknown_query
            in
            ForkedQuery.fallback_unless_invalid
              ~skip:config.fork_invalid_skips_seq_axiom_fallback_no_unknown_query
              ~fallback:(fun answer ->
                LadderSeqAxiomRlimit.with_ fallback_pair @@ fun () ->
                Z3Smt.Z3interface.with_seq_axiom_fallback
                  ~caller_timeout:(Some timeout) ~id:None (get_fenv ()) phi
                  answer)
            @@
            if refused then (
              probe_weakened phi;
              if weakened_proves ~timeout phi then `Valid
              else
              match config.fork_refused_questions_no_unknown_query with
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
          let ask_fresh = ask_fresh_within config.no_unknown_query_timeout in
          let ask_clause_by_pieces ?(refine = contextual_in_place) ?unproved
              ~what ~ask c =
            ClausePieces.ask_by_pieces ~refine
              ?max:config.clause_piece_bound_no_unknown_query ?unproved
              ~enabled:config.split_clause_heads_no_unknown_query
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
          (* [guarded_facts_ms_no_unknown_query]: a question the forward
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
            match config.guarded_facts_ms_no_unknown_query with
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
                            config
                              .guarded_facts_theory_facts_only_no_unknown_query
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
          Debug.print
          @@ lazy
               (sprintf "[no-unknown verdict] %d clause(s), sizes %s"
                  (List.length per_clause)
                  (String.concat ~sep:" "
                  @@ List.map per_clause ~f:(fun c ->
                         string_of_int (Ast.LogicOld.Formula.ast_size c))));
          (* Under [remember_proved_pieces_no_unknown_query]: for a rewritten
             clause asked by its pieces and not shown valid, the conjunction of
             the pieces left undecided (every other piece was shown valid), by
             the same index.  Valid exactly when the rewritten clause is, so a
             later stage may ask it in the clause's place. *)
          let remember = config.remember_proved_pieces_no_unknown_query in
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
                if config.onepoint_split_no_unknown_query then
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
            (* With [two_pass_budget_no_unknown_query], every form is asked
               first at the short budget and only the ones that ran out of it
               again at the full one; see [first_proved]. *)
            (* With [fork_seqinst_questions_no_unknown_query], a form is asked
               in a forked copy killed at the larger of the field and the
               question's budget (at the budget plus a margin with
               [fork_seqinst_kill_margin_no_unknown_query], so that the
               first pass's short budget holds in the copy too); only the
               verdict comes back, and anything but
               [`Valid] is reported as undecided, which [prove_valid] reads as
               it reads every answer but [`Valid] *)
            let fresh_within =
              match config.fork_seqinst_questions_no_unknown_query with
              | None -> ask_fresh_within
              | Some kill_ms ->
                  fun timeout phi ->
                    let ms =
                      ForkedQuery.ladder_kill_ms ~floor:kill_ms
                        ~margin:config.fork_seqinst_kill_margin_no_unknown_query
                        ~timeout
                    in
                    (* only the solver call is forked, and asked there with no
                       Z3 timer (the thread serving it does not exist in a
                       forked process), the kill being its budget; the shape
                       test and the sequence-axiom fallback stay in-process, as
                       without the field *)
                    let native ~timeout:_ phi = forked_native ~ms phi in
                    note_asking ~kind:"forked" timeout phi;
                    budgeted @@ fun () -> fresh_body ~native timeout phi
            in
            let ask, second_pass =
              match config.two_pass_budget_no_unknown_query with
              | None ->
                  ( ask_form (fresh_within config.no_unknown_query_timeout),
                    None )
              | Some ms ->
                  ( ask_form (fresh_within ms),
                    Some
                      ( (function `Timeout -> true | _ -> false),
                        ask_form (fresh_within config.no_unknown_query_timeout)
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
            (* With [case_split_index_budget_no_unknown_query], the index-case
               questions are asked at that budget (never above the form's own),
               so that a case the solver decides only slowly counts as
               undecided and the form is then asked whole; reset on the way
               out, so that no later ladder asks with this one's solver *)
            SeqInstantiation.index_case_ask :=
              Option.map config.case_split_index_budget_no_unknown_query
                ~f:(fun ms ->
                  let ask_case =
                    ask_form
                      (fresh_within
                         (Int.min ms config.no_unknown_query_timeout))
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
                      config.instantiate_sequence_premises_no_unknown_query
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
          (* The quick sweep (see [quick_sweep_no_unknown_query]): every
             clause, piece by piece, at a short budget, stopping at the first
             refutation; a clause whose pieces are all shown valid is recorded.
             Asked exactly as the long questions below ask ([ask]), only with a
             smaller budget, so an answer here is one of theirs. *)
          let quick_sweep () =
            match config.quick_sweep_no_unknown_query with
            | None -> None
            | Some (per_query, whole) ->
                enter_phase "quick";
                let deadline =
                  Common.Clock.now_s () +. (Float.of_int whole /. 1000.)
                in
                let ask_short phi = budgeted @@ fun () ->
                  pointwise_refute ~timeout:per_query phi
                  @@ axioms_first phi @@ fun phi ->
                  let phi = factor_eqs ~timeout:per_query phi in
                  (if config.seq_as_array_no_unknown_query then
                     Z3Smt.Z3interface.check_valid_seq_as_array
                   else Z3Smt.Z3interface.check_valid)
                    ~timeout:(Some per_query) ~fresh_solver:false ~id:None
                    (Ast.LogicOld.get_fenv ()) phi
                in
                NoUnknownLadder.quick_sweep
                  ~finish_started_clause:
                    config.quick_sweep_finish_clause_no_unknown_query
                  ~past_deadline:(fun () ->
                    Float.(Common.Clock.now_s () >= deadline))
                  ~pieces_of:(fun c ->
                    if config.split_clause_heads_no_unknown_query then
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
          (* The questions [exact_forms_first_no_unknown_query] moves ahead of
             the long unrewritten ones: each clause not yet shown valid asked in
             its rewritten form, piece by piece, then the sequence instantiation.
             Every answer taken from them is one the ladder below would take
             from the same question later -- a refutation only from an exact
             rewrite, a proof only of validity -- so moving them changes which
             answer is reached within the time, never which answer is right. *)
          let exact_forms_first () =
            if not config.exact_forms_first_no_unknown_query then None
            else
              let () = enter_phase "early-rewritten" in
              (* at the short budget under [two_pass_budget_no_unknown_query]:
                 a piece that runs out of it is asked again at the full budget
                 by the rewritten pass further down, which every run reaches
                 when nothing before it decides *)
              let ask_early =
                match config.two_pass_budget_no_unknown_query with
                | None -> ask_fresh
                | Some ms -> ask_fresh_within ms
              in
              (* the question asked of a skipped clause under
                 [early_rewritten_refute_skipped_no_unknown_query]: the pass's
                 own fresh question at its own budget, without the proof-only
                 word forms added below, since only a refutation is read *)
              let ask_skipped = ask_early in
              (* With [word_instances_first_no_unknown_query], each question of
                 this pass is asked first through the words of its
                 quantifier-free matched-instance forms (each a strengthening,
                 and the words question weaker than its form, so only a proof
                 is read), then as it is *)
              let ask_early =
                if not config.word_instances_first_no_unknown_query then
                  ask_early
                else fun phi ->
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
                        config.word_instances_two_rounds_first_no_unknown_query
                      piece
                  in
                  let by_words c =
                    let c =
                      if config.onepoint_split_no_unknown_query then
                        Ast.Evaluator.elim_onepoint_and_split_binders c
                      else c
                    in
                    if
                      Z3Smt.Z3interface.reads_int_as_word c
                      && Set.is_empty
                           (Ast.LogicOld.Formula.quantified_sort_env_of c)
                    then (
                      note_asking ~kind:"words" config.no_unknown_query_timeout
                        c;
                      budgeted @@ fun () ->
                      Z3Smt.Z3interface.check_valid_by_words
                        ~timeout:(Some config.no_unknown_query_timeout)
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
                  else ask_early phi
              in
              let refuted =
                (match config.early_rewritten_full_major_every_no_unknown_query with
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
                              ?max:config.clause_piece_bound_no_unknown_query
                              ~max_pieces:
                                config.early_rewritten_max_pieces_no_unknown_query
                              ~refute_skipped:
                                config.early_rewritten_refute_skipped_no_unknown_query
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
                              Debug.print
                              @@ lazy
                                   (sprintf
                                      "[no-unknown verdict] early rewritten \
                                       pass: clause %d skipped for its pieces \
                                       and refuted by its one question"
                                      i);
                              Some (`Invalid model)
                          | `Skipped None ->
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
             of the ladder always have [no_unknown_refutation_timeout]; the
             early pins ([early_pins_no_unknown_query]) have a smaller one and
             a deadline. *)
          let seq_pin_refutation ~within ?expired:_ ?(early = false) () =
            let applicable =
              early && config.early_pins_require_applicable_no_unknown_query
            in
            let guess_question psi =
              match within () with
              | None -> `Undecided
              | Some timeout -> (
                  let r =
                    Z3Smt.Z3interface.with_rlimit ~label:"ladder"
                      config.no_unknown_query_rlimit
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
              ~enabled:config.pin_seq_lengths_no_unknown_query
              ?already_valid:
                (if applicable then
                   Some
                     (fun i -> i < Array.length clause_valid && clause_valid.(i))
                 else None)
              ?classify:
                (if applicable && config.pin_seq_lengths_from_model_no_unknown_query
                 then Some guess_question
                 else None)
              ?guess:
                (if config.pin_seq_lengths_from_model_no_unknown_query
                    && not applicable then
                   Some
                     (fun psi ->
                       match within () with
                       | None -> None
                       | Some timeout -> (
                           let r =
                             Z3Smt.Z3interface.with_rlimit
                               ~label:"ladder"
                               config.no_unknown_query_rlimit
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
                let r =
                  Z3Smt.Z3interface.with_rlimit ~label:"ladder" config.no_unknown_query_rlimit
                  @@ fun () ->
                  Z3Smt.Z3interface.check_sat
                    ~timeout:(Some timeout)
                    ~fresh_solver:true ~id:None (fenv_used_by psi) [ psi ]
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
              early && config.early_pins_require_applicable_no_unknown_query
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
                               config.no_unknown_query_rlimit
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
                (if config.drop_valid_premises_before_pin_no_unknown_query then
                   Some
                     (fun psi ->
                       match within () with
                       | None -> None
                       | Some timeout -> (
                           let r =
                             Z3Smt.Z3interface.with_rlimit
                               ~label:"ladder"
                               config.no_unknown_query_rlimit
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
              ~enabled:config.pin_scalars_no_unknown_query
              ~default_compound:config.pin_scalars_default_compound_values
              ~binder_free_relaxation:
                config.pin_scalars_binder_free_relaxation_no_unknown_query
              ~already_valid:(fun i ->
                i < Array.length clause_valid && clause_valid.(i))
              ~guess:(fun psi ->
                match within () with
                | None -> None
                | Some timeout ->
                let r =
                  Z3Smt.Z3interface.with_rlimit ~label:"ladder" config.no_unknown_query_rlimit
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
                  if config.onepoint_split_no_unknown_query then
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
          let relation_pin_refutation ~within ?expired ?(early = false) () =
            let ask_sat what psi =
              match within () with
              | None -> None
              | Some timeout ->
              let r =
                Z3Smt.Z3interface.with_rlimit ~label:"ladder" config.no_unknown_query_rlimit
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
              if early && config.early_relation_pin_precheck_no_unknown_query
              then
                Some
                  (fun psi ->
                    match ask_sat "shape precheck" psi with
                    | Some `Unsat -> true
                    | _ -> false)
              else None
            in
            let gc_every =
              if early then
                config.early_relation_pin_full_major_every_no_unknown_query
              else None
            in
            (match gc_every with
            | Some n -> Z3Smt.Z3interface.with_new_context_full_major_every n
            | None -> fun f -> f ())
            @@ fun () ->
            let applicable =
              early && config.early_pins_require_applicable_no_unknown_query
            in
            NoUnknownRelationPin.refute ~log:Debug.print ?expired ?infeasible
              ~by_length_vectors:
                (early
                && config.early_relation_pin_length_shapes_no_unknown_query)
              ~skip_relation_free_clauses:applicable
              ?cheap_infeasible:
                (if applicable then
                   Some
                     (fun psi ->
                       match ask_sat "applicability precheck" psi with
                       | Some `Unsat -> true
                       | _ -> false)
                 else None)
              ~enabled:config.pin_relations_no_unknown_query
              ~already_valid:(fun i ->
                i < Array.length clause_valid && clause_valid.(i))
              ~guess:(sat "shape guess")
              ~ask:(sat "pinned negation (sat is a refutation)")
              (Set.to_list @@ Ast.ClauseSetOld.to_formulas
              @@ Ast.ClauseSet.to_old_clause_set Map.Poly.empty
              @@ PCSP.Problem.clauses_of pcsp)
          in
          (* [stage] prefixes the ladder phases the three pins are traced
             under: [""] for the late pins, ["early-"] for the early ones *)
          let pins ?expired ?relation_budget ?per_pin_budget
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
              match relation_budget with
              | None ->
                  let within, expired = budget () in
                  relation_pin_refutation ~within ?expired ~early ()
              | Some (within, expired) ->
                  relation_pin_refutation ~within ?expired ~early ()
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
            pins ~stage:""
              ~within:(fun () -> Some config.no_unknown_refutation_timeout)
              ()
          in
          (* The same three pins asked once EARLY, right after the quick
             sweep and before the rewritten forms and the sequence
             instantiation, under [early_pins_no_unknown_query]'s
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
             ([early_point_pin_first_no_unknown_query],
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
            let per_query, whole = config.early_pins_budget_no_unknown_query in
            let within, expired =
              NoUnknownLadder.lazy_budget ~now:Common.Clock.now_s
                (per_query, whole)
            in
            let expired =
              if config.early_pins_stop_at_deadline_no_unknown_query then
                Some expired
              else None
            in
            let search_complete = ref false in
            let r =
              (match config.early_pins_full_major_every_no_unknown_query with
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
             [early_pins_budget_no_unknown_query] from when it starts, rather
             than all three sharing one from when the first starts.  Used by
             the raced copy of [early_pins_raced_no_unknown_query], which runs
             beside the process: the shared budget exists to bound how long the
             pins delay the ladder, and a copy delays nothing.  Why: with every
             clause still open (before the exact forms prove any), the
             sequence-length pin's questions on a Rust-derived bit-set input
             reached their 1 s caps on four clauses and spent the shared 10 s,
             leaving the point pin, the one that refutes it, about two. *)
          let early_pin_refutation ?(per_pin = false) () =
            match config.early_pins_no_unknown_query with
            | false -> None
            | true ->
                let per_query, whole = config.early_pins_budget_no_unknown_query in
                let fresh_budget () =
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
                    if config.early_pins_stop_at_deadline_no_unknown_query then
                      Some (fun () -> Option.is_none (within ()))
                    else None
                  in
                  (within, expired)
                in
                let within, expired = fresh_budget () in
                let per_pin_budget =
                  if per_pin then Some fresh_budget else None
                in
                let relation_budget =
                  Option.map config.early_relation_pin_budget_no_unknown_query
                    ~f:(fun budget ->
                      let within, expired =
                        if config.early_relation_pin_cpu_clock_no_unknown_query
                        then
                          NoUnknownLadder.cpu_budget ~now:Common.Clock.now_s
                            ~cpu:NoUnknownLadder.thread_cpu_seconds
                            ~max_scale:
                              config.early_relation_pin_max_scale_no_unknown_query
                            budget
                        else
                          NoUnknownLadder.lazy_budget
                            ~now:Common.Clock.now_s budget
                      in
                      ( within,
                        if config.early_pins_stop_at_deadline_no_unknown_query
                        then Some expired
                        else None ))
                in
                let relation_first =
                  config.early_relation_pin_first_no_unknown_query
                  && some_relation_clause ()
                in
                let r =
                  (match config.early_pins_full_major_every_no_unknown_query with
                  | Some n ->
                      Z3Smt.Z3interface.with_new_context_full_major_every n
                  | None -> fun f -> f ())
                  @@ fun () ->
                  pins ?expired ?relation_budget ?per_pin_budget ~relation_first
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
          (* The cheap pin question ([early_cheap_pins_first_no_unknown_query],
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
                let per_query, _ = config.early_pins_budget_no_unknown_query in
                let r =
                  Z3Smt.Z3interface.with_rlimit ~label:"ladder"
                    config.no_unknown_query_rlimit
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
          (* the race of [early_pins_raced_no_unknown_query], when started:
             finished (its copy killed, or the process parked when the copy
             has already taken the run over) before the verdict leaves *)
          let pins_race = ref None in
          let verdict =
            Exn.protect
              ~finally:(fun () ->
                Option.iter !pins_race ~f:PCSatCommon.ParallelRace.finish;
                pins_race := None)
              ~f:(fun () ->
            match quick_sweep () with
            | Some verdict -> verdict
            | None when Array.for_all clause_valid ~f:Fn.id -> `Valid
            | None ->
            (* the two early stages, in the order
               [early_pins_after_exact_forms_no_unknown_query] gives; either
               decides alone, so the order changes only when an answer is
               reached.  [conj_ask] below is the budget of the whole-conjunction
               questions, shortened under
               [conj_timeout_after_early_no_unknown_query] once the exact forms
               have run and left the problem undecided. *)
            let early_ran = config.exact_forms_first_no_unknown_query in
            let conj_ask ask_within phi =
              NoUnknownLadder.ask_conj
                ~timeout:
                  (NoUnknownLadder.conj_timeout
                     ~cap:config.conj_timeout_after_early_no_unknown_query
                     ~early_ran ~default:config.no_unknown_query_timeout)
                ~ask:ask_within phi
            in
            match
              NoUnknownLadder.first_decided
                (NoUnknownLadder.early_order
                   ~cheap_pins_first:
                     (config.early_cheap_pins_first_no_unknown_query
                     && config.early_pins_no_unknown_query
                     && config.pin_seq_lengths_no_unknown_query)
                   ~pins_raced:
                     (config.early_pins_raced_no_unknown_query
                     && config.early_pins_no_unknown_query)
                   ~point_pin_first:
                     (config.early_point_pin_first_no_unknown_query
                     && config.early_pins_no_unknown_query
                     && config.pin_scalars_no_unknown_query)
                   ~pins_after_exact:
                     config.early_pins_after_exact_forms_no_unknown_query
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
                                  let t0 = Core_unix.gettimeofday ()
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
                                          (Core_unix.gettimeofday () -. t0)
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
                      Option.map (early_point_pin_refutation ())
                        ~f:(fun model -> `Invalid model)
                  | NoUnknownLadder.Early_pins ->
                      Option.map (early_pin_refutation ()) ~f:(fun model ->
                          `Invalid model)
                  | NoUnknownLadder.Exact_forms -> exact_forms_first ())
            with
            | Some verdict -> verdict
            | None when Array.for_all clause_valid ~f:Fn.id -> `Valid
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
            match conj_ask ask_within asked with
            | (`Valid | `Invalid _) as verdict -> verdict
            | undecided -> (
                enter_phase "conj-opened";
                match conj_ask ask_within (open_single_cons_binders asked) with
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
                    | None -> enter_phase "late-seqinst"; seq_instantiation undecided
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
                            | None ->
                                enter_phase "late-seqinst";
                                seq_instantiation undecided)))))))
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
             [report_budget_exhaustion], on stderr; the result is whether that
             option turns a [timeout] into [unknown]. *)
          let budget_exhausted () =
            if !budget_cut = 0 then false
            else begin
              let msg =
                sprintf
                  "budget exhausted: %d of %d validity queries of the \
                   zero-unknown verdict ran out of their budget (%d ms wall \
                   clock each%s; coordinator fields no_unknown_query_timeout, \
                   no_unknown_query_rlimit)"
                  !budget_cut !budget_asked config.no_unknown_query_timeout
                  (match config.no_unknown_query_rlimit with
                  | None -> ""
                  | Some r -> sprintf ", rlimit %d" r)
              in
              Debug.print @@ lazy ("[no-unknown verdict] " ^ msg);
              (* opted into: the person who set the option asked for the
                 reason, and a reason behind a tracing flag is one they do
                 not have *)
              if config.report_budget_exhaustion then prerr_endline msg;
              config.report_budget_exhaustion
            end
          in
          (* The countermodel is recorded with witness terms for the
             refuted clause's universal binders when a certificate is asked
             for (see [CountermodelWitness]); finding them costs solver
             questions, so nothing is computed otherwise. *)
          let countermodel_witness model =
            if witness.WitnessConfig.unsat then
              Some
                (UnsatWitness.make ~problem:(Some pcsp) senv
                   (UnsatWitness.Countermodel
                      {
                        formula = phi;
                        model;
                        witnesses =
                          CountermodelWitness.find
                            ~timeout:(Some config.no_unknown_query_timeout) phi
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
              | Some model -> refuted_by model)
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
                if Set.is_empty bounds then None
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
                          config.no_unknown_query_rlimit
                        @@ fun () ->
                        Z3Smt.Z3interface.check_sat
                          ~timeout:(Some config.no_unknown_refutation_timeout)
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
            Ast.ClauseGraph.set_dedup_normalized version.graph
              config.dedup_normalized_examples;
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
                config.phase_list
                |> List.map ~f:(build_phase pcsp rl_config)
                |> Result.all
                >>| fun phase_list ->
                List.iter phase_list ~f:(function
                  | US (module MUS) ->
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
               A lazy pre-pass ([houdini_after_seconds]) is asked the same way
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
                      (* [houdini_in_parallel]: the copy that finds a solution
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

  (* [sweep_unknown_free_clauses]: see [UnknownFreeSweep].  [Some] only with
     a refutation, as [Unsat] with the refuted clause's countermodel. *)
  and sweep_unknown_free ?(witness = WitnessConfig.default) pcsp =
    if not config.sweep_unknown_free_clauses then None
    else
      let senv = PCSP.Problem.senv_of pcsp in
      let formulas =
        List.map ~f:Ast.Evaluator.split_seq_reads_for_validity
        @@ UnknownFreeSweep.formulas senv (PCSP.Problem.clauses_of pcsp)
      in
      if List.is_empty formulas then None
      else
        let per_query, whole =
          Option.value config.quick_sweep_no_unknown_query
            ~default:(500, 5000)
        in
        let started = Common.Clock.now_s () in
        let deadline = started +. (Float.of_int whole /. 1000.) in
        let ask phi =
          Z3Smt.Z3interface.with_rlimit ~label:"ladder" config.no_unknown_query_rlimit
          @@ fun () ->
          (if config.seq_as_array_no_unknown_query then
             Z3Smt.Z3interface.check_valid_seq_as_array
           else Z3Smt.Z3interface.check_valid)
            ~timeout:(Some per_query) ~fresh_solver:false ~id:None
            (Ast.LogicOld.get_fenv ()) phi
        in
        let result =
          UnknownFreeSweep.sweep ~split:config.split_clause_heads_no_unknown_query
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
              if witness.WitnessConfig.unsat then
                Some
                  (UnsatWitness.make ~problem:(Some pcsp) senv
                     (UnsatWitness.Countermodel
                        {
                          formula = piece;
                          model;
                          witnesses =
                            CountermodelWitness.find
                              ~timeout:(Some config.no_unknown_query_timeout)
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
