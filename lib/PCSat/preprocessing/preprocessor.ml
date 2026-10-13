(* PCSat's preprocessor: simplify a predicate constraint problem before the
   CEGIS loop sees it, and turn the loop's answer back into an answer about
   the problem as given.

   [solve solver pcsp] relativises the answer positions of admissible and
   integrable unknowns, runs [preprocess], hands the result to [solver], and
   extends a solution with the definitions of every unknown preprocessing
   removed (eliminated by resolution, or with arguments dropped or shared).
   [preprocess] is the pipeline, each pass behind its own configuration
   field: normalisation and clause simplification, rewriting of sequence
   reads, elimination of unknowns by resolution ([PvarEliminator]), the
   finite instantiation of universally quantified sorts, reduction of
   arguments (constant, determined, copied), elimination of trivial
   well-founded, parity and functional unknowns, clausal form and a final
   simplification.  It returns the problem and, when a pass already solved
   it, the solution.

   Contract.  Every pass preserves satisfiability under the per-model
   semantics: a problem is satisfiable when every model of the background
   theory admits an interpretation of the unknowns satisfying it, so a pass
   may replace the problem by [false] only from a refutation valid in every
   model, and a solution of the result must extend to one of the input.
   A pass that can only lose an answer -- a budget, a size bound, a refused
   question -- falls back to leaving the problem as it was.  A refutation
   the finite instantiation obtained from a nested solve is reported with a
   certificate of its own. *)
open Core
open Common
open Common.Util
open Common.Ext
open Ast
open Ast.LogicOld
open PCSatCommon

module Config = struct
  type t = {
    enable : bool; [@default true]
    verbose : bool; [@default false]
    resolution_threshold : int; [@default 4]
    simplification_with_smt : bool; [@default false]
    num_elim_bool_vars : int; [@default 0]
    relativise_prop_positions : bool; [@default true]
        (** give every clause with an admissible or integrable unknown the
            premise [0 <= t] for each real component [t] of each such
            application's answer argument (the last), whose source domain is
            the non-negative reals.  Read over [Real], a clause also demands
            the instances where that argument is negative, and a refutation
            resting on one is not a refutation of the source problem.  The
            premise removes exactly those instances, leaves the solution space
            as it is and loses no solution, so it is sound for both answers.
            Off only to measure what it changes; the solution checker reads
            the relativised problem either way *)
    encode_head_disjunctions : bool; [@default false]
        (** replace every disjunctive head by a skolemised choice witness of
            kind [FN] (an existential-witness encoding, equisatisfiable), so
            that a run measures what encoding the disjunction costs against
            keeping it; off, the disjunction is kept *)
    instantiate_quantified_premises : bool; [@default false]
        (** add to each clause the instances, at the terms it hands its
            unknowns, of the premises it states with a quantifier *)
    dedup_alpha_equivalent_disjuncts : bool; [@default true]
        (** drop disjuncts of a clause that differ only in the names of their
            bound variables, which merging clauses that share a premise
            produces; runs before the instantiation above *)
    cell_abstraction : int; [@default 0]
        (** replace each array argument of an unknown by this many (index,
            value) pairs, so that a solution which has to speak about every
            element of an array may be quantifier free in the abstracted
            signature -- the quantifier reappearing only when the solution is
            read back.  0 leaves the problem alone.

            Only a *satisfiable* answer may be taken from the abstracted
            system: a solution of it concretizes to one of the original, while
            the original may have a solution no formula over this many cells
            expresses, so an unsatisfiable answer says nothing.  The pass
            therefore tries the abstraction first and falls back to the
            original problem for any other answer. *)
    split_single_cons_clause_vars : bool; [@default false]
        (** replace every clause variable whose sort is a datatype with exactly
            one constructor (a tuple, a record, a reference wrapper) by that
            constructor applied to fresh field variables, recursively, and fold
            the selectors that then apply to a constructor.  An equivalence per
            clause (every value of such a sort is its constructor applied to
            its fields), so sound for both answers.  What it buys: a clause
            that hands an unknown [sel_1 v] and [sel_2 v] of one variable [v]
            yields examples over selectors applied to a parameter, which
            resolution cannot unify with anything but itself, where the split
            clause yields examples over two plain parameters.  Runs before the
            predicate elimination and the finite instantiation of quantified
            sorts; a problem that arrives already clausified is left alone *)
    split_single_cons_selected_only : bool; [@default false]
        (** with [split_single_cons_clause_vars], split only a clause variable
            that the clause reads through a selector (and, recursively, only
            the fields that are read through one); a variable the clause only
            passes whole stays as it is.  Each split is the same identity, so
            this changes which equivalent clause is produced, never its
            meaning *)
    cancel_seq_concat_equations : bool; [@default false]
        (** after the predicate elimination and again before the final
            normalisation, rewrite every sequence equation and disequation by
            cancelling the common prefix and suffix of its two sides' operands
            ([a ++ x = a ++ y] to [x = y]), exact since concatenation is
            cancellative.  Meant for [split_single_cons_clause_vars], whose
            plain field variables let the elimination substitute definitions
            [v1 = v0 ++ v3] and so build equations [v0 ++ w = (v0 ++ v4) ++ v3]
            that Z3 decides far less readily than [w = v4 ++ v3] *)
    finite_forall_sorts : bool; [@default true]
        (** try assuming a universally quantified sort has n elements, n upward,
            by substituting an n-constructor datatype for it and finitising
            everything over it -- quantified arrays, the unknowns' array-sorted
            arguments, and array reads at a variable index, and each functional
            unknown given as an uninterpreted function rather than as a relation
            with the axiom saying it is one: a solution must work for every
            type, so a refutation at one size refutes the system, while
            satisfiability at one size concludes nothing. **On by default**:
            measured over 131 dependently quantified files it refutes two that
            no configuration answered, loses none, changes no verdict and is
            slightly faster, and over 120 constrained Horn files -- which have
            no quantified sort for it to fix, so it returns them untouched -- it
            is exactly neutral. The search stops at the first size the solver
            cannot decide, the sizes above it being strictly harder *)
    finite_forall_sorts_by_name : bool; [@default true]
        (** let the pass above also run when a DATATYPE mentions the quantified
            sort -- which is what a front end that monomorphises by name emits,
            a datatype of arity zero whose selectors return the sort variable.
            That case used to be declined because substitution reached a
            datatype only through its parameters and so left the constructors
            behind; it is substituted correctly now, and the pass then decides
            questions it could not reach before.

            **On by default, and the measurement says it is free rather than
            profitable.** Over 213 dependently quantified files, on against off
            is 0 verdict disagreements, the same number of files unanswered on
            each side, 1.02x wall, and one file gained against one lost -- both
            of which are separately known to answer in 15 s or not at all,
            across repeated runs of one binary. So there is no signal either
            way, and what decides it is that a refutation route no shipped
            configuration reaches is not a route: the family this covers is the
            one the Rust front ends produce.

            It is **not** free by construction, and the one file lost is the
            shape to watch: the pass spends a solver query per size, so an input
            that used to answer just inside its budget can fall outside it. What
            it cannot do is change a verdict, since a refutation at one
            cardinality refutes the system and satisfiability at one concludes
            nothing.

            With it on, the singleton instance of the fused-iterator benchmark
            is decided `sat` in seconds, where the pass previously said nothing
            about it at all *)
    finite_forall_sorts_nested_solve : bool; [@default true]
    (* Hand an instance the single query could not decide to a nested solve,
       using only a refutation from it.

       This switch does not PRODUCE wrong answers, but it can REACH one the
       solver gives: the instances are arrays indexed by the finite datatype
       the pass itself creates, and a solver may answer an equality between
       two array literals over such a sort WRONGLY -- `sat`, with its own model
       contradicting it -- which a resolution step reads as permission to
       refute a satisfiable problem.  Such an equality is rewritten into the
       conjunction of its reads before it is asked.  The two cases call for
       opposite work and a corpus differential cannot tell them apart; running
       the same instance through none of this code can.

       On by default.  Over the 42 dependently quantified files that declare a
       quantified sort, one binary with this field as the only difference,
       90 s one file at a time: 0 verdict disagreements, 31 answered on each
       side, 1.07x wall -- almost all of which is the eleven files that use
       their whole budget on both sides.  No answer is gained by it on those
       files: the one input that answered only with it answered a wrong
       `unsat` reached through the array-literal equality above (its
       two-element instance is satisfiable), which the rewrite removes.

       What the measurement does not cover, because no input in it has the
       shape: a caller that runs two constraint-solving calls at once, each
       reaching this pass.  The environment swap below is a blind overwrite,
       so two such calls would silently take each other's datatypes.  That
       hazard is not this switch's -- the pass above installs the same
       environment for its own query and is on by default -- but this switch
       lengthens the window from one query to a whole nested solve. *)
    finite_forall_sorts_nested_solve_budget : int option; [@default Some 10000]
    (* A wall-clock budget in milliseconds for each nested solve above, or
       [None] for none.  The nested solve is used only for a refutation, so a
       run past the budget is discarded exactly as a satisfiable instance is,
       and the budget cannot change a verdict -- only whether a refutation is
       found.  Checked by the CEGIS loop between phases, so a single phase that
       does not return is not cut short.

       The value is read off a census of every tracked dependently quantified
       file declaring a quantified sort (220 files, one run each, the ladder
       timed per size): the nested solve ran on 28 of them and was bimodal.
       The 24 that decided returned within 4.7 s (the 5 refutations within
       1.2 s); the 4 that did not decide were
       still running when the run's 45 s ended, the main solve never having
       started.  Ten seconds is twice the slowest decided answer and eight
       times the slowest refutation. *)
    finite_forall_sorts_nested_solve_strict_budget : bool; [@default true]
    (* enforce the budget above inside a phase too: the synthesizer's retry
       loop yields once it has passed, and each of its solver calls is capped
       by the time left.  Off, a synthesis step that keeps failing can hold a
       nested solve far past its budget -- measured: ten seconds granted, still
       running after 150, the main solve never started. *)
    finite_forall_sorts_nested_solve_budget_after_first_round : int option;
        [@default Some 2000]
    (* [Some ms]: once the nested solve's first CEGIS round has ended without
       an answer, shorten its budget to [ms] milliseconds from its start; the
       first round itself is bounded only by the budget above.  [None]: off.

       A short budget pays on a satisfiable instance, where the nested solve
       can only refute and decides nothing: on three generic loop inputs it
       ran 12-22 s over 3-8 rounds and was still undecided.  A short budget
       given from the start costs refutations, because the refutations seen
       come in the first round (an instance refuted in 0.7-0.9 s, round 0, in
       three of three runs) and that round's wall time is not stable on a
       loaded machine: one run took 4.4 s, the 2 s budget cut it, and the
       main loop never refuted the problem.  Granting the first round the
       full budget keeps those refutations and still stops a nested solve
       that has gone a round without one. *)
    finite_forall_sorts_nested_solve_fresh_context : bool; [@default true]
    (* run each nested solve above on a solver context of its own, cleared
       before it and restored after it, where the caller supplies such a
       solver (the constraint solver's own entry point does).  The context
       carries the example graph and truth tables from one solve to the next,
       and without this the MAIN solve started from the nested solve's
       examples about the instance: on one input whose instance is satisfiable
       in 0.3 s the main solve then answered 0 of 8 across four builds where
       with the nested solve off it answered 5 of 8.  Removing inherited
       examples can only remove premises a refutation might rest on. *)
    finite_forall_sorts_query_timeout : int; [@default 2000]
    (* the budget in milliseconds of the single solver call deciding each size
       before the nested solve is tried.  Bimodal in the same census: the
       18 decided calls all returned within 0.12 s, while of the 28 undecided
       ones 21 gave up at once and 7 spent the whole
       budget (it was 10 s, which was most of a satisfiable input's time before
       its main solve began -- the nested solve after it then took 0.5 s).
       A call that times out hands the size to the nested solve, which decides
       it too when it can. *)
    finite_forall_sorts_max_instance_size : int option; [@default None]
    (* a guard against building an instance nothing can read: [Some m]
       declines a size [n] when the problem's tree size (its abstract syntax
       counted as a tree, before anything is substituted) times [n] exceeds
       [m], and, the sizes above it being larger, every size after it.
       Declining is the [Undecided] a timeout gives, without the nested solve,
       which would build the same instance as a problem.  The pass only ever
       transfers a refutation, so declining can lose one and change no verdict.
       [None] (the default) builds every size.  What it guards: on a Thrust
       input of 125 clauses whose text is 2 MB after elimination, building the
       one-element instance took about 20 s before its 2 s query, which then
       timed out, and the nested solve after it 13 s more, with nothing
       concluded. *)
    finite_forall_sorts_fork_query : bool; [@default true]
    (* ask the single solver call deciding a size in a forked copy killed
       after its budget whenever the instance may not return
       ([Z3interface.may_not_return], a quantifier over a sequence, say), and
       read back only the verdict: [unsat] refutes the size as before, [sat]
       decides it (no model is used), and a killed copy is [Timeout], which
       hands the size to the nested solve as a timeout does.  Why: the
       solver's own budget does not hold over such an instance -- on a
       Rust-derived [try_fold] whose one-element instance quantifies over
       sequences the 2 s call ran past 300 s and the run never left
       preprocessing.  Sound: only the verdict crosses, and only [unsat]
       transfers.  Off: the call is made in this process as before. *)
    finite_forall_sorts_charge_construction : bool; [@default false]
    (* charge building a size's instance to [finite_forall_sorts_query_timeout]:
       the budget is a deadline from the start of that size, read between the
       construction's steps (the sort substitution, each round of the
       finitising loop and each step in it), and the query gets what is left.
       Past it the size is answered [Timeout] exactly as the query running out
       is today, so the nested solve, with its own budget, is still tried.  A
       single step that does not return, or the conversion of the finished
       instance for the solver, is not cut short.  Off (the default) the budget
       covers the solver call alone, and building the instance is unbounded.
       Sound for the same reason as above: only a refutation transfers. *)
    finite_forall_sorts_parallel : bool; [@default false]
    (* run the finite instantiation in a forked copy raced against the rest of
       the run ([PCSatCommon.ParallelRace]), instead of before it.  The pass
       is refutation-only: it returns the problem it was given, or [false]
       when some size of the quantified sorts has no solution.  So the copy
       answers only when it refutes, and then continues with [false] exactly
       as the sequential order continues after a refutation; the process goes
       on at once with the problem as given, which is what the sequential
       order does whenever the pass refutes nothing.  Every answer the race
       can give is one the sequential order can give.  What changes is when
       the pass's time is spent: on a satisfiable input it is spent beside the
       run rather than before it (6-14 s of preprocessing before the raced
       Houdini copy could start, on a Rust-derived [try_fold] loop whose one
       unknown only that pre-pass answers).  The copy holds the process's heap
       copy-on-write, so its memory counts against the run's.  Raced only when
       [preprocess] is handed a place to leave the race ([finite_race]), so
       that the caller finishes it before its answer leaves; never inside a
       solve bounded by a deadline, nor on the measurement route that
       substitutes a size instead of deciding it. *)
    refute_by_unfolding_parallel : bool; [@default false]
    (* run the unfolding refutation ([refute_by_unfolding], with its doubling
       pass) in a forked copy raced against the rest of the run, as
       [finite_forall_sorts_parallel] does for the finite instantiation, and
       for the same reason: the pass only refutes, so the copy answers only
       with the refuted problem and continues from there as the sequential
       order would, while the process goes on at once with the problem as
       given.  On a satisfiable input its time (3-8 s under load, most of it
       the doubling pass's forked questions, on a Rust-derived [try_fold]
       loop) is spent beside the run rather than before the raced Houdini
       copy starts.  Raced under the same conditions as the finite
       instantiation (a place to leave the race, no deadline-bounded solve). *)
    finite_forall_sorts_targeted_instance : bool; [@default true]
    (* build the instance problem the nested solve is handed by substituting
       only into the clauses whose sorts, binders, symbols, unknowns or applied
       functions reach a quantified sort, leaving the others as they are (no
       round trip through the other term representation).  Exact: the instance
       is the one substituting into every clause gives, structurally and after
       the nested solve's normalisation, on random problems and on every
       quantified-sort input of the corpus that can be read.  The saving is
       small: building the instance is a fraction of a second on the problems
       that reach this pass after elimination, and the slow part of a size is
       building the single query's formula, which this does not touch.  Off:
       every clause is converted and substituted. *)
    elim_one_sided_fn_preds : bool; [@default false]
        (** replace a functional predicate that every clause uses only as a
            premise, at distinct variables, by an existential over its result.
            Equisatisfiable, but it removes the predicate without being able to
            define it, so a [sat] model no longer mentions it and the solution
            checker can only report that constraint unchecked -- off by default
            because measuring it found no verdict it earns and five models it
            stops being able to check *)
    add_fn_totality_consequences : bool; [@default true]
        (** add the existential obligation that the totality of a clause's
            functional premises forces on it, when a model falsifies that
            obligation and so refutes the system. Adds a clause and removes
            nothing, so no model loses a definition *)
    drop_implied_body_atoms : bool; [@default false]
        (** after the other passes, drop a premise [q(t)] of a clause when
            another premise [q(s)] of the same clause is an instance of it by
            a substitution for variables occurring nowhere else in the clause.
            The clause [forall v. q(s) /\ q(t) /\ phi => H] is then equivalent
            to [forall v. q(s) /\ phi => H]: the private variables are
            universal, so the dropped premise stands for [exists v'. q(t)],
            which [q(s)] witnesses.  The resulting clause is also a
            consequence of the original by instantiation, so a solution or a
            refutation of the new system is one of the old.  Elimination by
            resolution leaves such copies behind -- a loop step whose premise
            is duplicated with fresh variables for the parts nothing else
            reads -- and a copy turns a clause with one premise into one with
            two: a goal clause then yields no negative example but an
            undecided two-atom clause, and a step clause resolved against a
            positive example leaves the copy as a residual premise instead of
            a new positive *)
    unify_negated_linear : bool; [@default false]
        (** let the unifier that resolution and the clause graph use solve a
            negated linear term ([-(1 - x)] and its siblings) for its
            variable ([LogicOld.unify_negated_linear]); off, such a term
            matches only itself.  Sound either way.  Wanted with
            [split_single_cons_clause_vars]: the fresh field names it
            introduces change which side of a linear equation the elimination
            solves, and the loop step [p x => p (x + 1)] came out as
            [p (-(1 - y)) => p y], which no positive example unified with, so
            no example was resolved forward through it.  Set process-wide
            when a solve starts, also for the solving loop after it *)
    condense_up_to_linear : bool; [@default false]
        (** let condensation compare integer subterms up to their linear
            normal form, also inside constructor applications
            ([ClauseOld.condense_up_to_linear]); off, they must be
            syntactically equal.  Exact either way.  Wanted with
            [split_single_cons_clause_vars], whose resolvents keep a premise
            copy whose only difference from the kept premise is [-1 + x]
            against [-(1 - x)].  Set process-wide when a solve starts *)
    condense_final_clauses : bool; [@default false]
        (** after the other passes, condense every clause once more
            ([ClauseOld.condense]: drop a literal of which another literal of
            the same polarity is an instance by a substitution for variables
            occurring nowhere else in the clause, integer arguments compared
            up to their linear normal form).  An equivalence of each clause.
            Wanted with [split_single_cons_clause_vars]: once a tuple's fields
            are separate variables, the elimination leaves a premise copy
            whose private fields are those of the kept premise, beside it,
            with one shared argument spelled [-1 + x] in one and [-(1 - x)]
            in the other, so the per-resolvent condensation, which compared
            terms syntactically, kept both; a one-premise loop step became a
            two-premise one and examples resolved through it stopped meeting.
            Before condensing, an equation between two integer variables that
            the normal form writes [0 != x - y] is applied as a renaming
            ([ClauseOld.merge_int_var_equations]), since a copy may differ
            from the kept premise only by it *)
    condense_resolvents : bool; [@default true]
        (** in the predicate eliminator, condense every resolvent: drop a
            literal that another literal of the same polarity and clause is an
            instance of, by a substitution for variables occurring nowhere
            else in the clause.  An equivalence of the clause (the argument is
            at [ClauseOld.condense]).  Where [drop_implied_body_atoms] removes
            such a premise once from the final clauses, this removes it from
            each intermediate resolvent too, so a copy sitting on a predicate
            that is eliminated later is gone before that elimination resolves
            it, and the occurrence counts the elimination rules decide from
            never see one premise twice.  It changes the clause set every
            later phase sees, which is why it waited for a corpus sweep
            before becoming a default *)
    condense_pure_resolvents : bool; [@default true]
        (** in the predicate eliminator, after [condense_resolvents], condense
            the pure part of every resolvent ([ClauseOld.condense_pure]): drop
            the disjuncts that mention a set of variables occurring in no atom
            when a renaming of those variables maps each of them onto a
            disjunct that stays.  An equivalence of the clause.  Wanted where
            a chain of definitions each mentions every earlier one: each
            elimination inlines the earlier definitions once directly and once
            through every later definition, and the pure part doubled with
            each predicate eliminated on a straight-line Thrust input (sizes
            1,297 / 2,567 / 4,911 / 9,851 / 19,503 over five consecutive
            eliminations).  On by default: four such inputs of 27 measured
            went from no answer in five runs to an answer in four or five,
            and none lost one *)
    condense_pure_unknown_free_resolvents : bool; [@default false]
        (** with [condense_pure_resolvents], condense also a resolvent that
            applies no unknown.  Off: such a resolvent is a clause the
            zero-unknown verdict asks Z3 about as it stands, every variable of
            it is one no atom reads, and condensing it replaces its own
            variables by the copies the eliminations made of them.  The
            result is equivalent, but on three Thrust inputs the verdict's
            ladder then split one of those clauses into 40 pieces where it had
            split the uncondensed one into far fewer, two of the pieces ran
            out of budget, and the inputs it answered in 20-60 s timed out at
            120 s.  The doubling condensation is wanted against happens in
            resolvents that still apply an unknown, and is removed there *)
    condense_pure_max_search_nodes : int option; [@default None]
        (** with [condense_pure_resolvents], the number of search calls one
            condensation of a resolvent may make, over all its seeds
            ([ClauseOld.condense_pure ~max_search_nodes]); past it the search
            stops and the resolvent keeps the condensations found so far,
            still an equivalence.  [None]: no bound.  Why: the normalisation
            budget below does not bound the search, since an image already
            normalised costs no check, and on a Thrust input with arity-27
            loop invariants one condensation backtracked through cached images
            for more than two minutes, the rest of the run's 300 s; a bound
            per seed did not stop it, the resolvent having hundreds of seeds *)
    elim_dedup_alpha_disjuncts : bool; [@default true]
        (** in the predicate eliminator, drop from each resolvent the
            disjuncts that repeat an earlier one up to the names of their
            bound variables ([PvarEliminator.AlphaDedup.disjuncts]), after the
            first simplification and again on each clause of its clausal form
            before condensation.  An equivalence of the clause.  Wanted where
            a closed quantified premise -- a [:law] the reader inserts into
            every clause that may depend on its function -- reaches many
            clauses: each clause carries it with binders of its own, so the
            copies resolution unions into a resolvent differ only by bound
            names, and neither set merging nor condensation, which compare
            disjuncts syntactically, removes them.  On by default (an exact
            rewrite); [false]: resolvents as built *)
    elim_joint_prune_doomed : bool; [@default false]
        (** with [elim_joint_condense], stop enumerating a partial closure of
            joint seeds once a live disjunct whose variables are all bound or
            fixed by it has no live image ([ClauseOld.condense_pure
            ~joint_prune_doomed]): every closure extending it would be refused
            at the hand-over's image test.  Every result is still an exact
            condensation, but not always the same one: the steps it saves
            under the per-pair closure bound reach closures the unpruned
            enumeration never reached, and the normalisation count moves.  On
            a Thrust resolvent with 43,131 refused closures one condensation
            took 32 s against 176 s with the same result; off by default
            until measured *)
    elim_joint_condense : bool; [@default true]
        (** with [condense_pure_resolvents], let the condensation of each
            resolvent's pure part also drop a set of atoms together with the
            disjuncts over their variables, under one substitution mapping the
            atoms onto kept atoms of their polarity and the disjuncts onto kept
            disjuncts ([ClauseOld.condense_pure ~joint]); exact (the clause is
            equivalent to the result in every model).  For a straight-line
            chain of contexts each premising every earlier one, whose
            eliminations otherwise double each use's atoms and constraints.
            Process-wide and only ever turned on. *)
    condense_pure_memo_failures : bool; [@default true]
        (** with [condense_pure_resolvents], remember each failed call of the
            condensation search with the state of every variable its
            execution read, and answer a later call with the same touched
            disjuncts that agrees on those variables as failed without
            searching it ([ClauseOld.condense_pure ~memo_failures]).  The
            search is a function of what it reads, so such a call would fail
            the same way: wherever the search ends within its budgets it
            returns the same condensation, in no more search calls; where a
            budget cuts it short it may find more, still an equivalence.
            Why: on a Thrust input with arity-28 loop invariants one
            condensation re-searched the same failing group of variables under
            every combination of bindings of unrelated variables chosen before
            it, for minutes (26,709 search calls become 6,434 with the same
            result).  On by default (an exact speedup) *)
    condense_pure_max_checks : int; [@default 20_000]
        (** with [condense_pure_resolvents], the number of normalisations one
            condensation of a resolvent may spend
            ([ClauseOld.condense_pure ~max_checks]); past it the resolvent is
            returned with the condensations found so far, which is still an
            equivalence.  The default 20,000 is the function's own.  On a
            Thrust loop input whose eliminations ran 17 condensations of
            resolvents of 13-27 disjuncts, the five that reached the bound
            took 2-5 s each, 13 of the 18 s spent condensing on a lightly
            loaded machine and most of a 120 s budget under heavy load, and
            dropped two literals or none; the calls that ended on their own
            used 2,600-17,000 *)
    condense_pure_shape_candidates : bool; [@default true]
        (** with [condense_pure_resolvents], bind a variable of the search
            only to a variable some disjunct holding it can line up with
            ([ClauseOld.condense_pure ~shape_candidates]): the variable
            printed at the same place in a live disjunct of the same normal
            form shape, a variable of a disjunct of the same symbols in
            another order, or (a merge) another variable of the disjunct or
            its image.  The rest of the search is unchanged and a found
            renaming is checked as before, so the result is exact; what is
            given up is a merge of two variables onto a third that neither
            disjunct mentions.  On by default: on a Thrust loop input the
            unrestricted search spent 28 s of a run in 17 condensations, most
            of them ending at the normalisation budget, and under a second
            with the restriction *)
    condense_pure_shape_commutative : bool; [@default false]
        (** with [condense_pure_shape_candidates], also let a variable line
            up with every variable of a same-shaped disjunct that plays the
            same role there up to the order of the summands
            ([ClauseOld.condense_pure ~shape_commutative]).  The normal form
            orders a sum's summands by variable name, so a renamed copy whose
            variables cross another one in name order prints the same shape
            with two equal-coefficient summands swapped, and the printed
            alignment then offers only the wrong partner.  On a 32-step
            straight-line Thrust input this blocked every condensation from
            the 13th elimination on: the resolvents grew from 889 to 3,229
            nodes and condensing took over 70 s, where the unrestricted
            search kept them under 900 nodes.  Only widens the candidates the
            restriction allows, so the result stays exact *)
    condense_pure_inclusion_candidates : bool; [@default true]
        (** with [condense_pure_resolvents], bind a variable [u] of the search
            only to a variable [y] of an inclusion relation computed once per
            pass over a resolvent, in place of the printed alignment of
            [condense_pure_shape_candidates]
            ([ClauseOld.condense_pure ~inclusion_candidates]): [y] stays a
            candidate of [u] while every live disjunct holding [u] either
            holds [y] (a merge) or has a disjunct in which [y] plays [u]'s
            role up to the order of summands and every other variable has a
            partner of its role among its own candidates.  The relation is
            name-free, so a renamed copy whose variables cross another one in
            name order is still aligned.  A found renaming is checked by
            normalisation as before, so the result is exact; what is given up
            is the same merge of two variables onto a third that the shape
            restriction gives up.  On by default: over five runs each it
            answered an input whose condensation the name-ordered alignment
            left to the time limit, and lost none *)
    split_seq_reads : bool; [@default true]
        (** in the predicate eliminator, ask each validity question of the
            clause simplification after substituting a clause's definitions of
            sequence variables and splitting every read of a concatenation by
            index ([Evaluator.split_seq_reads_for_validity]); both preserve
            validity, so the question is the same one.  What it buys: a
            question whose one read of [s ++ [x]] sits under a quantified
            hypothesis about [s] was undecided in five of six z3 seeds and
            spent the 5 s budget three times per run on the Thrust call-site
            queries, and split it is decided in all six at 0.01 s.  A decided
            simplification changes the clause set every later phase sees:
            under the template chain without cells it lost a Thrust slice
            loop's refutation (3 of 3 answered without it, 0 of 3 with it,
            60 s), and under the cell template it still costs that refutation
            at 300 s (2 of 5 with it, 4 of 5 without).  On by default, that
            cost accepted: with pinned sequence lengths in the zero-unknown
            verdict it refutes a nested-sequence query no other setting
            decides. *)
    resolution_complete_max_clauses : int; [@default 100]
        (** when elimination by resolution stops because every remaining
            unknown would grow the clause set past [resolution_threshold],
            try resolving ALL of them away anyway, keeping the result only if
            no unknown is left and the clause set never exceeded this many
            clauses; otherwise the clause set and the recorded definitions
            are put back as they were.  Resolution is an equivalence of
            satisfiability whatever the threshold, so this is sound for both
            answers; what it changes is the question the rest of the run is
            asked -- a validity check of finitely many clauses, decided by
            the zero-unknown verdict, in place of a search for solutions in a
            hypothesis space that may not contain one (a solution needing an
            existential, for instance).  0 leaves the threshold alone.  100
            by default: over 325 Thrust, quantified-invariant and CHC inputs
            at 120 s it answered 284.4 expected against 282.6 without, with
            no verdict disagreement; the Thrust fuse queries went from 0 of 5
            to 5 of 5, and the files it answered less often each moved by one
            run of five. *)
    resolution_complete_prebound : bool; [@default false]
        (** inside the complete elimination above, before resolving an
            unknown away, predict the clause set's size as the clauses that do
            not mention it plus [pc * nc] (its positive times its negative
            occurrences, the threshold's own accounting) and abandon the
            attempt, building and asking nothing of that step, when the
            prediction exceeds [resolution_complete_max_clauses].  The
            prediction is exact when every resolvent becomes one clause that
            simplification keeps and no two coincide; where simplification
            drops resolvents (proved valid) it is too large and the switch can
            abandon an attempt the full build would have kept, and where a
            resolvent splits into several clauses it is too small and the full
            build's own test still applies.  Either way the answer cannot
            change, only whether the rest of the run is asked about the
            eliminated clause set.  What it buys: a step resolving 512 or 768
            resolvents, each with a validity question of seconds, is not built
            when it is predicted to exceed the bound.  Off: the test is only
            the one after each step is built. *)
    resolution_complete_early_exit : bool; [@default true]
        (** inside the complete elimination, stop building a step as soon as
            the clause set built so far exceeds
            [resolution_complete_max_clauses], instead of finishing the step
            and testing then.  Exact: the resolvents are simplified in the same
            order, the set only grows while it is built, so the attempt is
            abandoned with it on exactly when it is abandoned with it off, and
            kept with the same clause set otherwise; what it saves is the
            validity questions of the resolvents after the bound is crossed. *)
    resolution_complete_budget_ms : int option; [@default None]
        (** a wall-clock budget, in milliseconds, for one complete elimination
            attempt, read before each step and before each resolvent's
            simplification; when it is spent the attempt is abandoned as if it
            had exceeded its bound (the clause set and the recorded definitions
            put back).  A load-dependent cut, so unlike the two switches above
            it can change which clause set the rest of the run is asked about
            between two runs; never the soundness of the answer.  [None] sets
            no budget. *)
    pvar_elim_valid_timeout : int; [@default 5000]
        (** the wall-clock budget, in milliseconds, of each validity query the
            predicate eliminator asks while simplifying a clause
            ([PvarEliminator.check_valid]).  An undecided query keeps every
            disjunct of the clause, so a budget that runs out costs a
            simplification and never a wrong verdict; but the clauses that are
            left are what the rest of the run -- the zero-unknown verdict
            among it -- is asked about, so under load a query decided on an idle
            machine can leave a harder clause set behind *)
    pvar_elim_valid_rlimit : int option; [@default None]
        (** a Z3 resource limit ([rlimit], a count of the solver's own steps,
            independent of load) per query of the same checks, beside the
            wall-clock budget, which stays; [None] sets none *)
    pvar_elim_seq_axiom_rlimit : int option; [@default Some 650000]
        (** a Z3 resource limit per question of the sequence-axiom fallback
            asked by the same checks (see [pvar_elim_seq_axiom_fallback_ms]),
            beside the fallback's wall-clock budget, which stays as the kill
            for a check Z3 does not interrupt.  Separate from
            [pvar_elim_valid_rlimit] because the fallback asks the axiomatised
            form in a context of its own, so its count is another quantity.
            An exhausted limit leaves the question as the native check left
            it.  [None] sets none *)
    pvar_elim_valid_fresh_quantified : bool; [@default false]
        (** ask each quantified validity query of the same checks in a Z3
            context of its own instead of a pooled one.  Z3's work on a
            quantified query depends on what the context it is asked in has
            held before: one question of a Rust-derived input took 85,658
            resource units on a new context, 668,679 after one earlier
            preprocessing of the same input in the same context, and anywhere
            from 181,900 to 2,448,825 after two, so the same question was
            decided in 0.3 s in one run and ran out of its 5 s budget in
            another, and the clauses the preprocessing left differed.  A
            context of its own makes the work a function of the question; the
            price is a new context (and the collection before it) per
            quantified query.  A choice of where to ask, never of what a
            decision says. *)
    pvar_elim_valid_memo : bool; [@default true]
        (** remember, for the rest of one elimination call, the answer of each
            validity query of the same checks, and answer a repeated query
            from the record instead of asking the solver again.  The
            eliminator re-simplifies every clause after each elimination step
            and after each round of its outer loop, so a clause no step
            touches is asked the same question again with the same budget;
            where the question runs out of budget (a pure clause of a few
            hundred disjuncts over sequences, left behind once every unknown
            is resolved away), each repetition costs the whole budget and
            decides nothing.  A recorded answer is one the solver gave to an
            equivalent formula, and an undecided answer only keeps a clause's
            disjuncts, so the record can cost a simplification and never the
            soundness of a verdict.  Only a proof of validity and a refusal to
            ask are recorded at once; an invalid answer is quick and is asked
            again, because skipping those asks changed how later queries in
            the shared solver context went.  A timeout is not recorded as the
            answer at once but asked again with a short budget
            ([pvar_elim_valid_memo_reasks]): answering it from the record
            kept a clause the next ask would have proved in a twentieth of a
            second, and the zero-unknown verdict then spent its budget on
            that clause.  On by default: over 359 Thrust, quantified-invariant and CHC
            inputs at 120 s it answered 302.4 expected against 301.2 without, with no
            verdict disagreement. *)
    pvar_elim_valid_memo_reasks : int; [@default 4]
        (** with [pvar_elim_valid_memo], how many more times a query that ran
            out of its budget is asked before the record answers it as
            undecided.  A decided answer, and a shape the solver is not asked
            about, are recorded at once; a timeout is not, since one query's
            text can run out of the full budget twice and then be proved in a
            twentieth of a second *)
    pvar_elim_valid_memo_reask_timeout : int; [@default 500]
        (** the budget, in milliseconds, of each such repeated ask *)
    pvar_elim_valid_warm_reask_ms : int option; [@default None]
        (** [Some ms]: each validity question of the predicate elimination is
            first asked with a budget of [ms] milliseconds (at most
            [pvar_elim_valid_timeout]) and without the sequence-axiom
            fallback; if that is undecided it is asked again AT ONCE, in the
            same pooled solver, with the rest of [pvar_elim_valid_timeout] and
            the fallback as configured.  A question recorded as undecided is
            then answered from the record and never asked again, so the
            repeated asks of [pvar_elim_valid_memo_reasks] do not happen.
            Why: a quantifier-free question undecided at 5 s in a solver of
            its own, under every seed, was decided in 0.03 s when asked again
            in a new scope of the solver that had tried it inside a scope for
            100 ms or more (and not after a first try of 10 ms, nor after a
            reset); every decided check in two traced eliminations took at
            most 0.32 s.  So the re-ask is a two-phase solve, which this
            makes deliberate rather than a later repeat that lands in a
            solver other questions have used in between.  [None] (the
            default): one ask with the full budget, repeated as above. *)
    pvar_elim_valid_memo_reask_max_disjuncts : int; [@default 64]
        (** with [pvar_elim_valid_memo], a timed-out query is asked again only
            when it has at most this many disjuncts; a larger one is answered
            as undecided from the record after its first timeout.  A repeated
            ask costs more than its budget -- one to three seconds of
            conversion and solving around a 500 ms budget on a clause of a few
            hundred disjuncts over sequences -- and on such clauses no repeated
            ask has been seen to decide: a pure clause of 634 disjuncts, asked
            three times in each of four keys, spent about forty seconds of
            preprocessing on repeated asks that all ran out and pushed the
            zero-unknown verdict, which proves the clause valid piece by
            piece, past the run's time limit.  The query seen proved on a
            repeated ask was a single disjunct, a conjunction of 497
            characters that ran out of five seconds and was proved in 0.04 s on its
            third ask.  The default is 64; [Int.max_value] asks every timed-out
            query again, whatever its size. *)
    pvar_elim_valid_memo_alpha : bool; [@default true]
        (** with [pvar_elim_valid_memo], key the record up to a renaming of the
            question's variables, free and bound, as well as up to the order
            of its disjuncts and of each quantifier block: validity is a
            property of the universal closure, which such a renaming does not
            change, so two clauses that differ only in their variables' names
            share one answer.  Off keeps the key that is only up to the
            orders. *)
    pvar_elim_valid_defer_pure_min_disjuncts : int option; [@default Some 256]
        (** during predicate elimination, a clause with no predicate
            application whose validity question has at least this many
            disjuncts is not asked: it is kept whole, which an undecided
            answer does too, so no verdict can change by it.  Such a clause is
            counted by no elimination rule, so keeping it changes no
            resolution step.  At the last simplification of an elimination
            round it is asked as before (once, through the same record) when
            an unknown remains, so the search gets the clause set it gets
            without this; when no unknown remains it is left to the
            zero-unknown verdict, which decides the same question.  On a
            Thrust input whose five such clauses have 442 to 888 disjuncts,
            the questions decided 3 of 35 first asks over seven runs and took
            31-36 s of preprocessing per run.  [None] asks every clause. *)
    pvar_elim_seq_axiom_fallback_ms : int option; [@default None]
        (** during predicate elimination, the most the second attempt at an
            undecided validity question over sequences (the sequence-axiom
            fallback of the PCSat configuration's [seq_axiom_fallback]) may
            spend on one question, in milliseconds: [None] leaves the
            process-wide budget as it is, [Some 0] (or less) makes the
            elimination not ask the fallback at all, [Some n] asks it with at
            most [n].  Only an undecided answer is ever replaced by the
            fallback's proof, so the elimination's result can only differ by
            keeping a clause the fallback would have proved valid and dropped:
            cost and completeness, never soundness.  Every question the
            solver is not asked about (a quantifier over a sequence) still
            goes to the fallback, and on the Thrust inputs whose elimination
            takes 40-47 s those asks cost 0.65-2.6 s each against a 500 ms
            budget, about half of the elimination's validity time. *)
    pvar_elim_seq_axiom_fallback_budget_ms : int option; [@default Some 3000]
        (** during predicate elimination, the budget of the sequence-axiom
            fallback in milliseconds IN PLACE OF the process-wide one (the
            PCSat configuration's [seq_axiom_fallback], 500 ms by default),
            raised or lowered; the cap above and each question's own budget
            still apply, and nothing is asked when the process-wide fallback
            is off.  [None]: the process-wide budget.  Only an undecided
            answer is ever replaced by the fallback's proof, so this changes
            the time an undecided question costs and which clauses are proved
            valid and dropped, never soundness.  Why: on a Thrust input the
            fallback proves two resolvents valid in 0.6-0.8 s, which the
            500 ms budget leaves undecided under load, and the two clauses
            then reach the zero-unknown verdict, where one of them costs
            more than the rest of the run *)
    pvar_elim_seq_axiom_fallback_once : bool; [@default false]
        (** with [pvar_elim_valid_memo], a timed-out question that the record
            asks again does not ask the sequence-axiom fallback again unless
            the fallback's budget on the repeated ask would be larger than on
            the first, which it is not under the default budgets (the fallback
            runs with the smaller of its own budget and the question's, 500 ms
            both times).  The repeated native ask is unchanged.  Same
            soundness argument as above: not asking keeps the clause. *)
    pvar_elim_seq_axiom_fallback_after_refusal_only : bool; [@default false]
        (** during predicate elimination, ask the sequence-axiom fallback only
            for a question the solver was not asked about at all (a shape it
            may not return on), never after the solver was asked and ran out of
            its budget, and so never on a re-ask either, since only a timed-out
            question is asked again.  Why: on the Thrust inputs whose
            elimination takes 25-110 s, the fallback after a refusal proved
            about two thirds of the questions it was asked, and after a native
            timeout or a re-ask it proved none in the traces read, at 0.6-1.2 s
            each.  Same soundness argument as above: the fallback only turns
            an undecided answer into [`Valid], so not asking keeps the clause
            and changes no decided answer. *)
    pvar_elim_seq_axiom_fallback_charge_build : bool; [@default false]
        (** during predicate elimination, count the time the sequence-axiom
            fallback spends building its question (the translation, the
            negation normal form, the conversion of the goal) against the
            fallback's budget, and do not ask the solver once that budget is
            spent; otherwise the budget bounds the solver call alone.  Why: on a
            large Rust-derived input the build took about 2 s per question
            against a 500 ms budget, 37 of the 42 s the fallback cost there.
            Same soundness argument as above: a question not asked keeps the
            clause. *)
    pvar_elim_split_int_binders_at_ite : bool; [@default true]
        (** during predicate elimination, ask each validity question with
            every [forall x] / [exists x] over an integer whose body holds an
            [ite] on [x < c] (coefficient one; alone or inside a compound
            condition) split into the part below [c]
            and the part at or above it, the latter shifted by [x := x + c] so
            that it ranges from zero ([IntBinderSplit.rewrite]).  Exact: each
            split is an equivalence in every model, so an answer means what it
            meant.  Why: a read at [x - c] cannot be matched by a ground read,
            so the instance a proof needs ([x := k + c]) was found only by
            model-based instantiation, and one elimination question of a
            Rust-derived input was proved or not depending on the spelling of
            the sequence-axiom fallback's generated sort name and on the
            random seed; split, it was proved in about 50,000 resource units
            under every spelling and seed tried.  On by default *)
    pvar_elim_split_seq_prefix_over_concat : bool; [@default false]
        (** during predicate elimination, ask each validity question with every
            prefix extraction of a concatenation rewritten by the identity
            [extract (a ++ b) 0 k = ite (k <= len a) (extract a 0 k)
            (a ++ extract b 0 (k - len a))]
            ([Evaluator.rewrite_seq_prefix_over_concat]), before the solver
            and before the sequence-axiom fallback builds its own form.  Exact:
            the identity holds in every model, so the question asked is
            equivalent to the clause's and a [`Valid] or [`Invalid] answer
            means what it meant; only the clause's question is rewritten, never
            the clause.  Why: a quantifier-free question that z3 left undecided
            for 10 s under five seeds in a process of its own is a disjunction
            of two instances of this identity, and rewritten it is answered in
            under half a second under every seed. *)
    pvar_elim_fork_refused_ms : int option; [@default None]
        (** during predicate elimination, a validity question that
            [may_not_return] refuses (a quantifier binding a sequence, where no
            solver budget holds) and left unproved by the sequence-axiom
            fallback is asked all the same in a forked copy, in a fresh solver
            context with no Z3 budget, killed after the smaller of this many
            milliseconds and the question's budget; only a [`Valid] is read
            from it, and anything else leaves the question undecided.  [None] refuses it as before.  Sound: the copy's
            proof is the solver's proof of the same question, and a question
            left undecided keeps its clause.  Why: on a Rust-derived input every
            undecided elimination question (nine of nine) had been refused and
            then not decided by the fallback's form in 0.5 s, while asked
            natively in a process of its own z3 proved four valid (0.04-9 s) and
            refuted four (under 0.4 s) under five seeds. *)
    pvar_elim_words_first : bool; [@default true]
        (** during predicate elimination, a validity question that reads an
            integer as a word ([int_to_bv] of a non-numeral) is first asked
            through the words of its pieces' matched-instance forms
            ([SeqInstantiation.valid_by_word_forms]: the question split into
            its pieces by an exact rule, each piece and its one- and two-round
            matched forms asked by [Z3interface.check_valid_by_words] under
            the question's budget), and asked as before only when that proves
            nothing.  Only a proof is read: each form implies its piece and
            the words question is weaker than its form.  Why: on a bit-set
            input four of the five elimination questions left undecided
            (each 8-13 s with the native question, the sequence-axiom fallback
            and its build) read bits through [int_to_bv]; their clauses
            survive to the zero-unknown verdict, where the same obligations
            are proved through the words of their matched forms in under a
            second each.  On by default. *)
    pvar_elim_words_keep_proved : bool; [@default false]
        (** with [pvar_elim_words_first], the words route goes through every
            piece of the question instead of stopping at the first piece it
            does not prove, and the question then asked natively is the
            conjunction of the pieces it did not prove
            ([SeqInstantiation.words_by_pieces], written once per shared
            side by [pieces_with_residual]) instead of the whole question,
            when that rest is smaller than the question.
            Exact: the question is valid exactly when every piece is, the
            proved pieces are valid, so the question is valid exactly when
            the rest is; a proof or a countermodel of the rest is one of the
            question.  When no piece is proved, or the rest is not smaller,
            the whole question is asked, as before.  Why: one question's words route proved 23 of 32
            pieces over 52 s, failed on the 24th and discarded the 23 proofs
            before asking the whole question natively *)
    matched_skip_spent_searches : bool; [@default true]
        (** a matched-instance form (the words route's forms, and every other
            caller of [SeqInstantiation.matched_instance_form] in the process)
            skips the substitution search of an existential met once its
            pass's instance budget is spent
            ([SeqInstantiation.skip_spent_budget_searches]).  Exact: the
            search's answer is discarded then, so the same form is built, with
            the same fresh names, and the same questions are asked; only the
            time changes.  Why: on an elimination question of a Rust-derived
            coroutine input the words route spent 156 s of 213 s in 48,534
            such searches, of which 146 s were made after the budget was
            spent (10,790 of 12,594 searches).  On by default, being
            exact. *)
    pvar_elim_defer_pure_to_verdict : bool; [@default false]
        (** during predicate elimination, the validity question of a clause
            with no predicate application and no unknown is not asked while a
            round resolves (resolution never touches such a clause and no
            elimination rule counts it, so the question is the same at each
            simplification); at the round's last simplification it is asked
            as before when an unknown remains, and otherwise only through the
            words of its matched-instance forms (as [pvar_elim_words_first]
            asks them), only a proof read, the clause otherwise kept for the
            zero-unknown verdict.  Exact: an unasked question keeps its clause.
            Why: on a bit-set input three such questions stayed undecided at
            about nine seconds each (native budget, sequence-axiom fallback)
            and were asked again at later simplifications, while the verdict
            proved the same clauses, one by its pieces in under a second.
            Off by default *)
    pvar_elim_defer_pure_to_round_end : bool; [@default false]
        (** as [pvar_elim_defer_pure_to_verdict], with the round's last
            simplification asking the elimination's own question of each
            postponed clause whether or not an unknown remains: each pure
            clause is then asked once per round instead of at every
            simplification (an undecided one was asked again at the re-ask
            budget at each later simplification of its round).  Exact, for
            the same reason.  Off by default *)
    pvar_elim_words_full_major_every : int option; [@default None]
        (** while predicate elimination asks a question through its words
            ([pvar_elim_words_first], [pvar_elim_defer_pure_to_verdict]), the
            forced major collection before a new Z3 context is made before
            every n-th context only instead of before each; every words
            question is a context of its own, and on a bit-set input the
            collections were a fifth of the words questions' time (0.24 s
            each over the heap the elimination has built), most of them before
            questions that proved nothing.  The questions are the same; at
            most n dropped contexts wait for the collector at once.  [None]
            keeps the process-wide setting *)
    pvar_elim_implied_factor_equalities : bool; [@default true]
        (** during predicate elimination, each validity question is asked
            with the equations between the factors of its products that its
            linear facts imply (each shown by an [unsat] under the question's
            budget) stated as disjuncts [t != u]
            ([Z3interface.implied_factor_equalities]): an equivalence in
            every model, so every answer is one about the question.  Why:
            Z3's nonlinear arithmetic does not compare two products [n * t]
            and [w * i] once the linear part forces [n = w]; on a bit-set
            obligation the question ran past 30 s under two of three seeds
            and with [n = w] stated was answered in under 0.12 s under every
            seed.  On by default. *)
    pvar_elim_cvc5_retry_ms : int option; [@default None]
        (** during predicate elimination, a validity question Z3 left
            undecided (one refused by the shape test included, after the forked
            ask and the sequence-axiom fallback) is printed as SMT-LIB and given
            to cvc5 as a separate process with this many milliseconds of its own
            budget, killed by the wall clock one second later
            ([PCSatCommon.Cvc5Proof.valid_within]); only cvc5's [unsat] of the
            negation is read, as a proof, and anything else leaves the question
            undecided.  [None] asks nothing.  Sound: a proof is cvc5's proof
            of the same question in the same reading (out-of-range reads are
            open in both; a text with Z3's [seq.nth_u] is not asked), and an
            undecided question keeps its clause.  Why: on a Rust-derived input,
            nine of fifteen distinct undecided elimination questions that Z3
            left undecided at 10 s under five seeds in a process of its own were
            proved by cvc5 in 0.5-3.7 s under five seeds. *)
    elim_subsume_clauses : bool; [@default true]
        (** during predicate elimination, drop every clause whose literals
            (positive atoms, negative atoms, disjuncts of the pure part) are a
            superset of another clause's, compared syntactically under the same
            variable names: after the conjunctive normal form, after the
            one-sided and bound assignments, and on each resolution step's
            result.  Exact: the subsumer implies the clause it subsumes, so the
            clause set keeps its models, and a definition recovered for an
            eliminated predicate from the reduced set satisfies the original
            one.  What it buys: a body conjunct [discr = k => P payload] doubles
            the normal form, and once [P] is assigned [true] the copies differ
            only by pure literals, each a superset of one of them; on the Thrust
            fuse pair it takes resolution's input from 113 to 22 clauses and its
            largest step from 768 resolvents to 6. *)
    elim_subsume_hash_prefilter : bool; [@default true]
        (** [elim_subsume_clauses] by hashes first: each literal's hash, each
            clause's set of hashes, inclusion of the hash sets tested before
            the literal sets.  The same clauses are kept and dropped; only the
            structural comparisons of large literals are avoided.  On by
            default: on a Thrust closure input the polymorphic comparison of
            large formulas in subsumption took most of a 49-54 s bound
            assignment step, 31-33 s with the hashes *)
    elim_cnf_shared_fvs : bool; [@default true]
        (** the clausal form of predicate elimination reduces each clause's
            sort map with the free variables of its atoms and of its pure
            part's disjuncts remembered by physical identity across the call
            ([ClauseOld.reduce_sort_map_shared]): the same maps as without it.
            Why: the normal form gives thousands of clauses sharing large pure
            disjuncts, and their free variables were recomputed per clause,
            the largest part of a 24-31 s conversion on a Thrust closure
            input.  On by default (an exact speedup). *)
    elim_resolution_atom_pvs_memo : bool; [@default true]
        (** the resolution rounds of predicate elimination read each atom's
            predicate variables ([Atom.pvs_of]) through a table keyed by
            physical identity, kept across the rounds of one elimination:
            the same sets, so the same choices.  Why: the clauses a round
            leaves alone are the same values in the next, and walking every
            atom's argument terms once per round was most of the rounds'
            candidate choice on a Thrust closure input.  On by default (an
            exact speedup). *)
    elim_resolution_index : bool; [@default true]
        (** the resolution rounds of predicate elimination keep, across the
            steps of one chain, the clauses applying each predicate, the
            occurrence counts and each clause's interned literals
            ([PvarEliminator.ResolutionIndex]), so a step reads only the
            clauses applying the predicate it resolves and the new resolvents:
            the same counts, the same candidates and the same subsumption
            decisions, hence the same clause set built by the same insertions.
            Acts only with [elim_subsume_clauses].  Why: on a Thrust closure
            input whose clausal form has 2,400 clauses of 9.4 million nodes,
            each step resolving an auxiliary predicate in a few clauses spent
            0.14-0.97 s walking the whole set (counting occurrences and
            subsuming); with the index that round's whole-set work fell from
            64 s to 8 s.  On by default (an exact speedup).  Off: every step
            counts and subsumes the whole set *)
    elim_subsume_interned : bool; [@default true]
        (** the subsumption of [elim_subsume_clauses] with every literal
            interned once per call to an integer by a table whose equality is
            the literal sets' own polymorphic [compare], each clause's literal
            set an ascending id array, and each kept clause indexed under its
            literal occurring in the fewest clauses of the call.  The same
            clauses are kept and dropped, and the result is built by the same
            insertions, as without it (and as with
            [elim_subsume_hash_prefilter], which it takes precedence over).
            Why: on a Thrust closure input whose clauses share a large pure
            disjunct, the hashed version still tested every pair of clauses
            keyed by that disjunct, and subsumption was the largest single cost
            of a preprocessing that spent no time in the solver. *)
    elim_cnf_clause_tree : bool; [@default true]
        (** the clausal form of predicate elimination reads an input formula
            that is already one clause (a tree of disjunctions over
            unknown-free subtrees and signed applications of unknowns) in one
            pass ([Formula.cnf_of_clause_tree]): the same clauses as without
            it.  Why: a round after the first reads back the clauses the round
            before produced, and on a Thrust closure input with 2,376 of them
            the normal form walked every large pure disjunct once per
            disjunction above it. *)
    elim_set_aside_cnf_clauses : int option; [@default None]
        (** [Some n]: in each round of predicate elimination, an input formula
            whose clausal form is predicted to have more than [n] clauses is
            set aside -- not put in clausal form, and no unknown it mentions
            eliminated in that round -- and returned unchanged beside the
            round's result; after the last round they are put in clausal
            form once.  Sound for any [n]: eliminating a different set of
            unknowns keeps satisfiability.  It differs from the switch-off
            result where an unknown of a set-aside formula would have been
            eliminated, and where the resolution, no longer stopped by such an
            unknown's growth test, eliminates more.  Why: on a
            Thrust closure input whose inferred precondition occurs inside
            conjunctions under disjunctions, three formulas of 3,400-5,400
            nodes gave 2,142 of the 2,492 clauses and 9.0 of their 9.4 million
            nodes (the input's 93 formulas had 59,000), none of them touched
            by any resolution step since the precondition is never
            eliminated, and every pass of every round walked them clause by
            clause; with the switch the elimination ends in 30-45 s where it
            did not end in 300 s.  [None]: every formula is put in clausal
            form *)
    elim_set_aside_definitional : bool; [@default false]
        (** with [elim_set_aside_cnf_clauses = Some n]: a formula set aside
            is put in clausal form after the last round with fresh ordinary
            unknowns naming the conjunctions under its disjunctions whose
            distribution would multiply its clauses, each fresh [D(xs)] in
            place of its conjunction [C] and [D(xs) => C] beside it, applied
            again to what still exceeds [n] ([PvarEliminator.definitional_split]).
            Sound both ways: [C] occurs positively, so the new formulas imply
            the old one for any reading of [D], and reading [D] as [C] turns a
            solution of the old problem into one of the new; a solution is
            reported without the fresh unknowns' definitions mattering.  Not the
            same problem: the solver has the fresh unknowns to find.  Why: on a
            Thrust closure input, premises universally quantified over the
            inferred precondition became, once skolemised, conjunctions under
            the clause's disjunction, and three formulas gave 2,142 of the
            2,376 clauses every later stage walked one by one. *)
    resolution_max_growth : int option; [@default None]
        (** [Some b]: predicate elimination does not resolve away an unknown
            whose resolution is predicted to grow the clause set's node size
            by more than [b] -- each positive clause paired with each negative
            one, a resolvent counted as the two clauses' sizes together, less
            the clauses that leave -- and keeps it as a predicate the clauses
            go on applying.  Decided before the step is built.  Sound for any
            [b]: an unknown left in place leaves the same constraint, and the
            definitions recorded for the unknowns still eliminated are the
            ones resolution records without the guard (they may apply a kept
            unknown, whose solution the solver then supplies).  Why: on a
            Thrust coroutine input every program point's defining clause
            applies every earlier point's predicate again, the count test
            always allows a step with one positive occurrence, and inlining
            puts a renamed copy of an earlier body into a definition already
            holding one, so the largest clause doubled over four steps (4,463
            to 71,377 nodes) and the elimination did not end in 300 s.
            [None]: resolution is limited by occurrence counts only *)
    share_rebuilt_formulas : bool; [@default false]
        (** the passes that rebuild every formula of a problem keep the
            physical sharing of their input, each by a table keyed by node
            address that lives for one call: the round trips between the two
            term representations remember term images as well as formula
            images (and open their scope as [share_term_conversions] does),
            remembering an image only when computing it drew no fresh name.
            The output is the one the passes give without it, value for value
            and with the same fresh-name draws; only its sharing differs.
            Why: on an input whose elimination multiplies a clause into
            thousands, the clauses' large pure parts are one physical value
            when built, and each pass that rebuilt the formulas one by one
            made a copy per clause, so every later pass compared and walked
            the copies -- 2.3 million nodes as built, 50 million after one
            conversion *)
    triv_fn_linear : bool; [@default true]
        (** the pass that drops trivial functional body atoms reads the free
            variables of each of a clause's k functional body atoms once,
            rather than those of the k - 1 others for each of them (k^2
            walks), and the rest of the clause's only when some result is a
            variable; the same answers, so the same output.  Why: on a
            Thrust input whose clauses hold 21 to 33 such atoms over large
            arguments, the k^2 walks were most of a 150 s pass *)
    share_let_passes : bool; [@default false]
        (** inside [PCSP.Problem.normalize], the let passes (renaming let
            binders apart, putting lets in normal form, inlining lets whose
            definition applies an unknown) remember each node's result by
            physical identity under the same context, when computing it
            drew no fresh name; the same output, value for value and draw
            for draw, but shared where the input was *)
    share_term_conversions : bool; [@default false]
        (** the round trips between the two term representations that the
            preprocessing passes make over a whole problem
            ([PCSP.Problem.map_raw_old_exn]) keep physical sharing: each
            direction remembers the image of every formula node by physical
            identity inside one call ([Logic.ExtTerm.with_shared_term_conversion]),
            and the trivial-functional-predicate pass puts the whole problem
            in negation and clausal normal form inside one table
            ([with_shared_nnf_cnf]).  The same formulas up to physical
            sharing (and up to the bound names a beta-redex in a formula
            position draws when converted).  Why: a clausal form that
            multiplies alternatives gives thousands of clauses built from the
            same physical subformulas, and each per-formula conversion copied
            the shared parts once per clause, so a set held in megabytes as
            built held gigabytes after the elimination and every later pass
            walked and copied them *)
    shared_clause_dt_conversion : bool; [@default true]
        (** convert a clause from the higher-order to the first-order term
            representation inside one datatype-conversion scope, and a clause
            set (where it is converted as a whole) inside one scope, so the
            datatypes it mentions are converted once and shared
            ([Clause.shared_dt_conversion]): the same clauses up to physical
            sharing.  Why: an atom's conversion had no scope, so every datatype
            sort in it converted its whole datatype graph again; on a Thrust
            closure input the argument-sharing pass's conversion of 2,400
            clauses filled 6 GB.  On by default (an exact speedup: the
            converted clauses are equal, as values and as set trees, on every
            input checked).  Process-global once set.  Off: each atom's sorts
            converted separately *)
    elim_subsume_persistent : bool; [@default true]
        (** the subsumption of [elim_subsume_interned] with its interning
            tables kept from one call to the next (in a domain, from the start
            of an elimination), pruned after each call to the literals of the
            clauses kept, so that a literal met before is found by its physical
            identity and not hashed deeply again
            ([PvarEliminator.ClauseSubsume.reduce_persistent]).  The same
            clauses are kept and dropped, and the result is built by the same
            insertions, as with [elim_subsume_interned] (which it takes
            precedence over).  Why: the clauses a resolution step leaves alone
            are the same values in the next step, and on a Thrust input of 600
            clauses whose resolvents have over a hundred disjuncts, hashing
            every literal of every clause at every step was the largest part of
            a subsumption that took a fifth of the predicate elimination. *)
    elim_tautology_test : bool; [@default true]
        (** during predicate elimination, drop an input clause that is valid by
            a cheap syntactic test -- a head literal equal to a body conjunct,
            or two complementary disjuncts, an atom compared after
            [Evaluator.simplify] and [Normalizer.normalize] -- before its normal
            form is built, and a normal-form clause with an atom on both sides
            or complementary pure disjuncts.  Exact: a valid clause constrains
            nothing.  Such clauses are generated as obligations restating a
            body conjunct, and each is a negative occurrence of every predicate
            of its body. *)
    sweep_unknown_free_clauses_before_finite_instances : bool;
        [@default false]
        (** after predicate elimination and before the finite instantiation
            of quantified sorts, ask every clause that mentions no unknown for
            validity, each at 500 ms and all within 5 s
            ([PCSatCommon.UnknownFreeSweep]); a clause shown invalid refutes the
            problem, which is then handed on as the single constraint [false].
            The certificate is that bare leaf, which the checker reports as not
            re-derived.  Where the finite instantiation's nested solve runs, it
            can spend the whole run before the coordinator's own sweep
            ([sweep_unknown_free_clauses]) is reached *)
    sweep_unknown_free_clauses_before_elimination : bool; [@default false]
        (** the same sweep, asked once more BEFORE predicate elimination (after
            the kinds' own eliminations, on the clauses as normalised), with the
            same budgets and the same reading: a clause that mentions no unknown
            and is shown invalid refutes the problem, which is then handed on as
            the single constraint [false], so the elimination and the finite
            instantiation run on that one constraint.  Sound for the reason the
            later sweep is: no interpretation of the unknowns changes such a
            clause's truth value, so a model falsifying it is one in which the
            system has no solution.  What it buys is time and nothing else: on
            an input whose refuting clause mentions no unknown from the start,
            the elimination before the later sweep resolved one predicate whose
            negative occurrences were mostly in clauses holding it more than
            once, and did not return in 300 s, while the clause was refuted by
            one solver call of a few milliseconds. *)
    refute_by_unfolding : bool; [@default true]
        (** after predicate elimination and before the finite instantiation
            of quantified sorts (beside the sweep above), unfold every unknown
            that has a fact clause through its step clauses (a head and body
            atoms of that unknown only, such as a transitivity law) for
            [refute_by_unfolding_depth] levels, put the unfolding in place of
            the unknown in every goal clause whose atoms all have one, and ask
            each such unknown-free resolvent for a countermodel
            ([PCSatCommon.UnfoldRefute]).  A resolvent shown invalid refutes
            the problem, which is then handed on as the single constraint
            [false]: the unfolding implies the unknown in every solution of
            the facts and steps, so the goal is false under every
            interpretation in the countermodel.  It never concludes [sat].
            On the Thrust input this was written for (a client's claim about
            the tenth item a range of ten produces) the refutation needs ten
            facts chained by the transitivity law, and was found in 7 s at
            the defaults below. *)
    refute_by_unfolding_depth : int; [@default 12]
        (** the levels of the unfolding above: with
            [refute_by_unfolding_linear] [d] levels cover chains of up to [d]
            facts, without it a two-atom step doubles the formula per level
            and [d] levels cover chains of up to [2^(d-1)] *)
    refute_by_unfolding_counter_depth : int option; [@default Some 128]
        (** with [Some c], an unknown whose clauses carry a bounded counter
            (an integer argument that every fact sets to a literal [s], that
            every step, each with one body atom, increments by one under a
            guard [v < b]) is unfolded to the [b - s + 1] levels the counter
            allows, when that is deeper than [refute_by_unfolding_depth], at
            most [c] ([UnfoldRefute.counter_depth]); the size bound grows by
            the same factor.  A goal that needs the counter at its bound is
            reached at exactly that depth: on a loop counting the 64 bits of
            a word, the refutation needs 65 levels, where the default depth
            reaches 12.  Only the depth changes, so soundness is not at stake;
            it costs the larger unfolding on every input with such a
            counter, refutable or not. *)
    refute_by_unfolding_solve_linear : bool; [@default true]
        (** the one-point rule that removes a fact's or step's own variable
            from its unfolding level also applies to an integer equation in
            which that variable has coefficient 1 or -1 ([y = -a r] read off
            [a y + r = 0], [r] a linear sum of variables and a literal), and the
            substituted arguments are kept as flat
            integer sums ([BoundHoist.norm_term]).  Exact.  A counter step
            [x = k + 1] then passes [x - 1] down instead of a fresh [k], so
            every level of the unfolding speaks of the goal's own counter:
            on a loop counting the 64 bits of a word the 65-level resolvent
            has one counter variable instead of 65, and with
            [refute_by_unfolding_hoist_bounds] Z3 fixes it by propagation
            (refuted in about 2 s, where neither switch alone nor the default
            decides it within the step budget). *)
    refute_by_unfolding_hoist_bounds : bool; [@default true]
        (** before a resolvent is asked, the integer bounds its negation
            implies -- read through conjunction (intersection), disjunction
            (hull) and quantifiers ([BoundHoist.implied_bounds]) -- are made
            top-level conjuncts of the negation.  Exact (a formula is
            equivalent to its conjunction with what it implies); it puts the
            range of a word that every disjunct of an unfolding bounds where
            [z3_int_to_bv_range]'s bounded rule reads ranges, and the
            counter's range where Z3's propagation fixes it. *)
    refute_by_unfolding_linear : bool; [@default true]
        (** unfold only the first body atom of a step through the lower level
            and put the facts at the others, so that a level adds one copy of
            the level below.  The doubling form reached the same chain at
            depth 5 with a formula Z3 decided in no budget tried (up to 60 s
            on three seeds), where the linear one at depth 11 was decided in
            7 s *)
    refute_by_unfolding_timeout_ms : int; [@default 30000]
        (** the budget of each solver question of the unfolding above (at
            most three per resolvent): a resolvent is asked in a forked copy
            killed after three times this, since Z3's own timeout does not
            bound these questions over sequences *)
    refute_by_unfolding_budget_ms : int; [@default 60000]
        (** no resolvent is asked about once this much time has passed since
            the unfolding started, and the copy asking one is killed when it
            is reached *)
    refute_by_unfolding_max_size : int option; [@default Some 20000]
        (** with [Some m], an unknown whose unfolding has a level of more than
            [m] nodes gets none, and a resolvent of more than [m] nodes is not
            asked about ([UnfoldRefute.size_up_to]), so that the unfolding
            costs little on an input it cannot refute *)
    refute_by_unfolding_step_ms : int option; [@default Some 10000]
        (** with [Some n], the question of the unfolding above that decides a
            resolvent -- the validity question itself where the resolvent has
            no free sequence, the negation with the sequences' lengths pinned
            otherwise -- is killed after [n] ms ([UnfoldRefute.ask]'s
            [step_ms]); the relaxation that guesses the lengths keeps the
            budget above.  On inputs the unfolding does not refute, that
            question is where the pass spends its budget: one ran until the
            60 s kill on each of four Thrust inputs, while the refutation it
            is kept for takes 2.9 s in that question (and 7 s in the
            relaxation before it).  [None]: no bound of its own. *)
    refute_by_unfolding_fitting_doubling : bool; [@default true]
        (** when the unfolding above refutes nothing and its budget is not
            spent, a second pass over the same clauses in the doubling form
            (every body atom of a step unfolded through the level below,
            [refute_by_unfolding_linear] notwithstanding), up to
            [refute_by_unfolding_depth] levels, that keeps the levels below
            the first one over [refute_by_unfolding_max_size] and asks each
            goal at the deepest of them whose resolvent is within that bound
            ([PCSatCommon.UnfoldRefute.refute_fitting]), with the same
            questions, budgets and kill.  Sound for the reason the first pass
            is: every level implies the unknown in every solution of its facts
            and steps.  It never concludes [sat].  What it reaches that the
            first pass does not: a refutation through a step with two body
            atoms that needs the second atom unfolded too, at a depth whose
            doubling form fits the bound although the depth configured for
            the linear form does not.  [false] asks nothing more.  On by
            default: a Rust-derived loop's unsatisfiable twin was refuted in
            1-5 s instead of answering at 70-122 s through the CEGIS loop *)
    refute_by_unfolding_guess_ms : int option; [@default None]
        (** with [Some n], the relaxation above that guesses the sequences'
            lengths is killed after [n] ms ([UnfoldRefute.ask]'s
            [guess_ms]), and a resolvent whose relaxation is killed is left
            undecided.  It loses only refutations whose relaxation takes
            longer than [n] ms.  On a satisfiable Thrust input the relaxation
            (3,000 nodes, quantifier-free over sequences) ran until the
            pass's 60 s kill, which was the whole cost of the pass; the
            refutation the pass is kept for takes 7 s there.  [None]: bounded
            by the pass's budget only. *)
    word_range_invariants : bool; [@default true]
        (** before handing the preprocessed problem to the solver, find which
            integer arguments of the ordinary unknowns stay in
            [[0, 2^n)] for a width [n] some [int_to_bv n] of the problem
            uses (the greatest inductive subset of those ranges, asked of Z3
            clause by clause), add each such range as a premise of every body
            atom, and conjoin the ranges to the solution found
            ([PCSatCommon.WordRanges]; equisatisfiable, sound for both
            answers).  It is what lets [z3_int_to_bv_range] hand a body word
            to Z3 as a bit-vector rather than split it with an unbounded
            quotient *)
    word_range_invariants_timeout_ms : int; [@default 2000]
        (** the budget of each validity question of the pass above, asked in
            a forked copy killed at three times it *)
    elim_assign_before_cnf : bool; [@default true]
        (** during predicate elimination, substitute the constants the one-sided
            and bound steps assign (no positive or no negative occurrence, a
            valid lower bound, an unsatisfiable upper bound) into the input
            formulas and build the normal form again, instead of applying them
            to the normal form, whose copies of a disjunction around the
            assigned predicate are then already built.  Exact: the normal form
            of the substituted formulas is the substitution applied to the
            normal form, up to propositional simplification; the other
            definitions are found again on the rebuilt set. *)
    share_determined_pvar_args : bool; [@default true]
        (** drop an argument of an ordinary unknown when the clauses force
            every part of it to equal a part of another argument, and keep the
            forced equalities as a conjunct of the unknown's definition
            ([share_determined_pvar_args] below).  An argument that is a copy
            of another -- a mutable reference whose current and final values
            are also the first two fields of a tuple argument -- gives the
            array template a second set of cell columns for the same sequence,
            which doubles the index columns the cell guards are counted by.
            The converse follows: dropping a copy can bring a predicate under
            the bound on those columns and so give it guards it did not have,
            which a loop whose invariant needs none pays for in validation
            queries over the guarded candidates.
            Equisatisfiable (argued at the function), so sound for both
            answers; it asks one budgeted validity question per clause and
            candidate round.  On by default: over 360 Thrust, quantified-invariant and CHC
            inputs at 120 s it answered 306.0 expected against 305.2 without, with
            no verdict disagreement. *)
    share_determined_pvar_args_budget_ms : int option; [@default None]
        (** a wall-clock budget in milliseconds for the whole pass above,
            measured from its start: each validity question is asked with at
            most the time left (and at most its own 2 s), and once the budget
            is spent the pass stops asking and returns the problem unchanged,
            which is what it returns when it finds nothing.  The partial work is
            discarded rather than kept because it is not consistent: the
            candidate equalities are a greatest fixpoint, each round's survivors
            proved inductive only against the previous round's, so a set taken
            before the iteration has converged may contain an equality that a
            later round would have dropped.  [None] (the default) leaves the pass
            unbounded.  Measured on a Thrust input whose clauses are tens of
            kilobytes each: the pass asked 130 questions and nine fallbacks over
            56 s and was still running when the run was killed. *)
    share_determined_pvar_args_seq_axiom_fallback_ms : int option; [@default None]
        (** the cap on the sequence-axiom fallback (the second attempt at an
            undecided validity question over sequences) inside the pass above,
            as [pvar_elim_seq_axiom_fallback_ms] is for the predicate
            elimination: [None] leaves the process-wide budget as it is,
            [Some 0] (or less) asks no fallback there, [Some n] at most [n] ms.
            The fallback can only turn an undecided answer into [`Valid], so
            not asking it can only drop a candidate equality the pass would
            have kept: cost and completeness, never soundness.  On the input
            above nine fallbacks took 28.8 s, of which Z3 4.7 s. *)
    share_determined_syntactic_first : bool; [@default false]
        (** in the pass above, three changes to how its questions are
            answered, none to what they are.  (1) A candidate equality is
            kept without a solver when the clause's own definitions [x = t],
            selectors of their own constructors and the premise equalities
            rewrite its two sides to the same term ([ClauseCone.Normal]).
            (2) The rest are asked as a conjunction; a countermodel of it
            drops each candidate it falsifies by evaluation (only where every
            variable has a value in it and no symbol the theory leaves open
            occurs), and the conjunction of the survivors is asked again;
            when a countermodel drops nothing, or the question is undecided,
            they are asked one by one as without the switch, each
            countermodel tried on the candidates still to ask.  (3) A
            question whose inputs (the candidate lists it reads, which only
            shrink) are those of an earlier round is answered as then.  A
            syntactic proof is a proof and a countermodel refutes the
            one-by-one question, so wherever the solver decides the questions
            the pass keeps exactly what it keeps without the switch; where it
            leaves one undecided the switch can keep more (a syntactic proof
            or a decided conjunction), every kept equality proved. *)
    share_determined_memo_questions : bool; [@default false]
        (** in the pass above, ask each distinct question once: a question
            equal (after the simplification every question gets) to one the
            pass has already asked with the same time limit takes that
            question's answer, undecided included.  Every question is still
            one the pass without the switch asks; what the switch removes is
            the second and later asking of the same formula under the same
            limit, which the pass makes when several candidates of one head
            atom denote the same equation (the atom repeats an argument) and
            when a residual of one candidate is asked first as a one-element
            conjunction and then alone.  An undecided answer drops the
            candidate either way, so the result differs from the switch-off
            pass only where a second asking of an identical question would
            have been decided where the first was not. *)
    share_determined_slice_questions : bool; [@default false]
        (** with the switch above, first ask the conjunction of the
            candidates the syntax leaves on the premises connected to their
            variables only ([ClauseCone.slice]), keeping them all when that is
            proved (a proof of the slice is a proof of the whole question,
            whose premises it drops) and going on as above otherwise.  On the
            Thrust input it was built for the slices kept 58% of the premises
            and none was proved, so each cost one question more. *)
    drop_constant_args : bool; [@default true]
        (** after the predicate elimination, drop each argument of an
            ordinary unknown that every clause deriving it fixes to one
            closed constant or passes on unchanged from the unknown's own
            occurrence in its body ([DimReducer.drop_constant_args], where the
            equisatisfiability is argued): the unknown is replaced by a fresh
            one over the other arguments, each body occurrence gains the
            premise that the argument is the constant, and the answer reads
            the original back as the new one conjoined with that equation.
            Without it, every positive example carries the constant and the
            synthesizer separates the negatives by literals over such
            arguments rather than by the atoms an invariant needs.  Asks no
            solver.  [false]: no such reduction *)
    drop_fn_copy_args : bool; [@default false]
        (** after the argument reduction, drop each argument of a functional
            (or single-valued) unknown that is, at every occurrence and after
            the clause's own definitions [x = t], the same term as one fixed
            earlier argument or the same closed term
            ([DimReducer.drop_fn_copy_args], where the equisatisfiability is
            argued).  The argument reduction itself leaves these unknowns
            alone.  It matters for the witness predicates a universal in a
            clause body is skolemised into, which take every variable of the
            clause: on a Thrust input whose 36 witnesses had 1,402 arguments,
            990 were dropped, and the template initialisation went from 93 s
            to 9 s.  Asks no solver.  [false]: no such reduction *)
    restore_witness_universals : bool; [@default true]
        (** after the predicate elimination, put back the quantifier of a
            functional witness whose result now reaches only the pure parts
            of its clauses ([PCSP.Problem.restore_witness_universals], where
            the equivalence is argued): the clauses of one witness, which
            agree on everything but their pure parts, become one clause with
            [exists y. forall E. /\ phi_k] in place of the witness atom.  The
            witness stood for a body universal over an unknown that the
            elimination has removed; left in place, it is a function the loop
            must still learn.  Asks no solver.  [false]: no such step *)
    elim_fn_feeding_fn : bool; [@default false]
        (** drop a functional body atom (a witness of a skolemised body
            universal) whose result variable occurs only as a whole input
            argument of other functional body atoms, each applied once in the
            whole problem and each taking all of the dropped atom's inputs
            ([PCSP.Problem.elim_fn_feeding_fn_predicate], where the
            equisatisfiability is argued in both directions).  It is the shape
            left when the unknown the outer witness was for has been
            eliminated.  Asks no solver.  [false]: no such step *)
    elim_ite : bool; [@default false]
    propagate_lb_ub : bool; [@default false]
    reduce_pvar_args : bool; [@default true]
  }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "Preprocessor"

    (* a leaf: no nested config to load *)
    let instantiate = Or_error.return
  end)

  (* [make enable verbose resolution_threshold num_elim_bool_vars
     reduce_pvar_args] is the configuration of a preprocessor built inside a
     backend rather than read from a file.  Contract: every field is its
     [@default] above except the five given as arguments.  The record is read
     through the derived reader from an object that names only those five, so
     the defaults exist once, in the type, and a later change of a default
     reaches every caller of [make] too.  A caller that must hold a field
     differently says so at its call site with [{ (make ...) with ... }] and a
     comment giving the reason. *)
  let make enable verbose resolution_threshold num_elim_bool_vars
      reduce_pvar_args =
    match
      of_yojson
        (`Assoc
           [
             ("enable", `Bool enable);
             ("verbose", `Bool verbose);
             ("resolution_threshold", `Int resolution_threshold);
             ("num_elim_bool_vars", `Int num_elim_bool_vars);
             ("reduce_pvar_args", `Bool reduce_pvar_args);
           ])
    with
    | Ok config -> config
    | Error msg ->
        (* unreachable while every field has a [@default] (the five
           arguments too: they are passed so that a caller's choice does not
           depend on what the defaults are); a new field without one is
           reported here at the first call, naming it *)
        failwith ("Preprocessor.Config.make: " ^ msg)
end

module type PreprocessorType = sig
  val solve :
    ?witness:WitnessConfig.t ->
    ?bpvs:Ident.tvar_set ->
    ?oracle:PCSP.Problem.oracle ->
    ?nested_solver:(PCSP.Problem.t -> State.output Or_error.t) ->
    ?extend:bool ->
    (* passed on to [preprocess] (see there) *)
    ?post_elim:(PCSP.Problem.t -> PCSP.Problem.t) ->
    (?oracle:PCSP.Problem.oracle -> PCSP.Problem.t -> State.output Or_error.t) ->
    PCSP.Problem.t ->
    State.output Or_error.t

  val preprocess :
    ?witness:WitnessConfig.t ->
    ?bpvs:Ident.tvar_set ->
    (* [false] for a caller that does not ask whether the clauses are
       satisfiable (it only simplifies them and reads the unknowns back):
       the passes that would replace the problem by [false] are skipped *)
    ?refute:bool ->
    ?oracle:CandSolOld.t option ->
    ?normalize_params:bool ->
    (* a way to SOLVE a problem, for the one pass that can use one: the finite
       instantiation hands an instance its single solver call could not decide
       to a search, and takes only a refutation from it.  It is an argument
       rather than a call because this module is a dependency of the solver
       that would be called, so the direction has to be reversed -- and because
       a caller that has no solver (the printer, a backend that only prints the
       problem) then simply does not pass one, and the pass falls back to its
       query. *)
    ?solver:(PCSP.Problem.t -> State.output Or_error.t) option ->
    (* where the finite instantiation leaves the certificate of a refutation
       it obtained from [solver], when the refutation came with one; the
       problem returned is then [false], and the certificate says why *)
    ?finite_certificate:UnsatWitness.finite_instance option ref ->
    (* where the finite instantiation leaves the race it started under
       [finite_forall_sorts_parallel]; the caller passes [finish] over every
       race left here before its answer leaves.  Without it the pass runs in
       this process, in order *)
    ?finite_race:PCSatCommon.ParallelRace.t list ref ->
    (* a transformation of the problem right after predicate elimination,
       before every pass that follows it (argument reduction and sharing,
       the word ranges around the solver call): the caller's hook for an
       encoding that must not be seen by the elimination but must be seen by
       the rest.  Contract asked of it: the result is equisatisfiable with
       its argument in every model and keeps every unknown of it, so the
       elimination records and the argument logs still apply; an unknown it
       adds is reduced like one the elimination added.  When it is given, the
       clauses that mention no unknown are swept for a refutation first (as
       [sweep_unknown_free_clauses_before_finite_instances] does), and a
       refutation replaces the problem by [false] without applying it *)
    ?post_elim:(PCSP.Problem.t -> PCSP.Problem.t) ->
    PCSP.Problem.t ->
    (sort_env_map * (Ident.pvar * (sort_env_list * Formula.t)) Set.Poly.t)
    option
    * PCSP.Problem.t
end

(* the number of finite instantiations raced in a forked copy by this process
   ([finite_forall_sorts_parallel]); read by the tests *)
let finite_races_started = Atomic.make 0

(* the questions [share_determined_memo_questions] answered from an earlier
   identical one, over the process; read by the tests *)
let share_memo_hits = Atomic.make 0

(* how many times the unfolding refutation was started as a raced copy
   ([refute_by_unfolding_parallel]); read by the tests *)
let unfold_races_started = Atomic.make 0

(* Ids for the finite-instantiation queries, taken from above the range a solving
   run uses so that each query gets a solver instance of its own.  The pass runs
   before any solving domain is started, which is what makes an ordinary ref safe
   here. *)
let fresh_finite_query_id = ref 1_000_000

(* A census instrument for [share_determined_pvar_args], read by nothing:
   with [COAR_SHARE_CENSUS] set, one line per round of the pass's fixpoint on
   stderr, giving the head atoms asked about, their candidate equalities, how
   many of those the syntactic test proves, the summed and largest size of
   the questions asked whole and sliced (both with the premises as a list of
   conjuncts), the premises and those the slice keeps, the questions asked so far,
   and (with [share_determined_syntactic_first]) how many candidates fell back
   to the whole question, how many of those it proved, and how many head atoms
   were answered from an earlier round's identical question. *)
module Census = struct
  (* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
  let enabled = Lazy.from_val (Option.is_some (Sys.getenv "COAR_SHARE_CENSUS"))
  let on () = Lazy.force enabled

  type t = {
    mutable atoms : int;
    mutable cands : int;
    mutable syn : int;
    mutable hyp_sum : int;
    mutable hyp_max : int;
    mutable slice_sum : int;
    mutable slice_max : int;
    mutable premises : int;
    mutable kept : int;
    mutable memo : int;
    start : float;
  }

  let fresh () =
    {
      atoms = 0;
      cands = 0;
      syn = 0;
      hyp_sum = 0;
      hyp_max = 0;
      slice_sum = 0;
      slice_max = 0;
      premises = 0;
      kept = 0;
      memo = 0;
      start = Common.Clock.now_s ();
    }

  let atom st ~whole_size:hyp_size ~slice_size ~premises ~kept ~cands ~syn =
    st.premises <- st.premises + premises;
    st.kept <- st.kept + kept;
    st.atoms <- st.atoms + 1;
    st.cands <- st.cands + cands;
    st.syn <- st.syn + syn;
    st.hyp_sum <- st.hyp_sum + hyp_size;
    st.hyp_max <- Int.max st.hyp_max hyp_size;
    st.slice_sum <- st.slice_sum + slice_size;
    st.slice_max <- Int.max st.slice_max slice_size

  (* per kind of work: count, how many proved, seconds; the whole run *)
  let kinds : (string, int * int * float) Hashtbl.t =
    Hashtbl.create (module String)

  let timed kind ~valid secs =
    Hashtbl.update kinds kind ~f:(function
      | None -> (1, (if valid then 1 else 0), secs)
      | Some (n, v, t) -> (n + 1, (v + if valid then 1 else 0), t +. secs))

  let time kind f =
    if not (on ()) then f ()
    else
      let t0 = Common.Clock.now_s () in
      let r = f () in
      timed kind ~valid:false (Common.Clock.now_s () -. t0);
      r

  (* one line per head atom asked: the work so far by kind *)
  let progress () =
    Out_channel.eprintf "SHAREATOM %s\n%!"
      (String.concat ~sep:" "
         (List.map (Hashtbl.to_alist kinds) ~f:(fun (k, (n, v, t)) ->
              sprintf "%s=%d/%d/%.1f" k n v t)))

  let memo st = st.memo <- st.memo + 1

  let print_round st round questions =
    Hashtbl.iteri kinds ~f:(fun ~key ~data:(n, v, t) ->
        Out_channel.eprintf "SHAREKIND round=%d %s n=%d proved=%d secs=%.2f\n%!"
          round key n v t);
    Out_channel.eprintf
      "SHARECENSUS round=%d atoms=%d cands=%d syn=%d premises=%d kept=%d \
       whole_sum=%d whole_max=%d slice_sum=%d slice_max=%d questions=%d \
       memo=%d secs=%.2f\n%!"
      round st.atoms st.cands st.syn st.premises st.kept st.hyp_sum st.hyp_max
      st.slice_sum
      st.slice_max questions st.memo
      (Common.Clock.now_s () -. st.start)
end

(* raised inside [share_determined_pvar_args] when its budget is spent, and
   caught at its entry, which then returns the problem unchanged *)
exception Share_budget_spent

(* raised while building a finite instance when the size's budget is spent
   ([finite_forall_sorts_charge_construction]), and caught where the query is
   asked, which then answers [`Timeout] *)
exception Finite_construction_spent

(* A measurement instrument, off unless [COAR_FINITE_LOG] is set: one stderr
   line per size the finite instantiation of a quantified sort tries, with the
   single query's and the nested solve's answer and wall-clock time, which is
   what choosing a budget for the nested solve has to be read from. *)
(* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
let finite_log_enabled =
  Lazy.from_val (Option.is_some (Stdlib.Sys.getenv_opt "COAR_FINITE_LOG"))

let finite_log f =
  if Lazy.force finite_log_enabled then (
    Out_channel.prerr_endline ("[finite-sorts] " ^ f ());
    Out_channel.flush stderr)

(* THE FINITE INSTANCE OF A PROBLEM, as one function shared by the pass that
   builds it and by the checker that re-derives it, so that a certificate is
   checked against the instance the same code would build rather than against a
   copy it carries.

   [smap] sends each universally quantified sort variable to an enumeration
   datatype with n nullary constructors.  Everything a sort lives in is
   substituted: the clauses and their variables, the unknowns' argument sorts,
   the datatypes (field sorts included, since a front end that monomorphises by
   name writes arity-zero datatypes whose fields are the variable itself) and
   the recursive functions.  The kinds are kept, the instance being the same
   system read in a model whose carriers for those sorts are finite.

   Given [dtenv] and [fenv], the environments the problem was built in, the
   first function gives the environments the instance is read in, and the
   second the instance over them.  The substitution is exact; the caller is to
   have the substituted environments installed process-wide while anything
   reads the instance, since terms resolve datatypes and functions by name
   there. *)
let finite_instance_envs smap dtenv fenv =
  ( Map.Poly.map dtenv ~f:(LogicOld.Datatype.subst_sorts smap),
    Map.Poly.map fenv ~f:(fun (args, ret, body, is_rec, prop) ->
        ( List.map args ~f:(fun (x, srt) -> (x, Term.subst_sorts_sort smap srt)),
          Term.subst_sorts_sort smap ret,
          Term.subst_sorts smap body,
          is_rec,
          Formula.subst_sorts smap prop )) )

(* [clause_reaches_sort_key smap ~exi_senv ~fenv] over-approximates which
   formulas of a problem the finite instance can change: [false] for a formula
   whose own variables' sorts, binders, symbols and the unknowns and recursive
   functions it applies reach no key of [smap].  The round trip of such a
   formula through [LogicOld] with [subst_sorts smap] gives it back with every
   sort it names unchanged.  [fenv] is the function environment the problem
   was built in, before any substitution: the substituted one no longer
   mentions the keys.  A variable that is none of a clause variable, a binder,
   an unknown or a function of [fenv] counts as reaching. *)
let clause_reaches_sort_key smap ~exi_senv ~fenv =
  let keys svar = Map.Poly.mem smap svar in
  (* keyed structurally: equal sorts give equal answers, and a problem has
     few distinct sorts however many copies of each it holds.  A key the table
     cannot compare (one holding a function value) is judged every time. *)
  let memoise compute =
    let tbl = Hashtbl.Poly.create () in
    fun key ->
      try
        match Hashtbl.Poly.find tbl key with
        | Some r -> r
        | None ->
            let r = compute key in
            Hashtbl.Poly.set tbl ~key ~data:r;
            r
      with Invalid_argument _ -> compute key
  in
  let sort_reaches = memoise (Logic.ExtTerm.sort_reaches_svar keys) in
  let fun_memo = Hashtbl.Poly.create () in
  let fun_reaches x =
    Hashtbl.Poly.find_or_add fun_memo x ~default:(fun () ->
        match Map.Poly.find fenv x with
        | None -> true
        | Some (args, ret, _, _, _) ->
            List.exists
              ((ret : LogicOld.Sort.t) :: List.map args ~f:snd)
              ~f:(Term.sort_reaches_key smap))
  in
  (* symbols repeat (connectives, literals, a datatype's constructors), so
     each is typed once *)
  let sym_reaches =
    memoise (Logic.ExtTerm.sym_may_reach_svar ~sort_reaches)
  in
  fun (uni_senv, phi) ->
    Map.Poly.exists uni_senv ~f:sort_reaches
    || Logic.ExtTerm.term_may_reach_svar ~sort_reaches ~sym_reaches
         ~free_var_reaches:(fun x ->
           if Map.Poly.mem uni_senv x then false
           else
             match Map.Poly.find exi_senv x with
             | Some s -> sort_reaches s
             | None -> fun_reaches x)
         phi

(* [~targeted:true] substitutes only into the formulas
   [clause_reaches_sort_key] says the substitution can reach, given [fenv],
   the function environment the problem was built in, and leaves the others as
   they are; the problem it returns is the one [~targeted:false] returns, which
   substitutes into every formula. *)
let finite_instance_problem ?(targeted = false) ?fenv smap ~dtenv_substituted
    ~fenv_substituted pcsp =
  let subst_unknown_sort so =
    let args, ret = Logic.Sort.args_ret_of so in
    Logic.Sort.mk_fun
      (List.map args ~f:(fun s ->
           Logic.ExtTerm.of_old_sort @@ Term.subst_sorts_sort smap
           @@ Logic.ExtTerm.to_old_sort s)
      @ [ ret ])
  in
  PCSP.Problem.map_params
    ~f:(fun params ->
      {
        params with
        PCSP.Params.senv =
          Map.Poly.map params.PCSP.Params.senv ~f:subst_unknown_sort;
        (* and the environments the problem carries, not only the
           process-global ones: a consumer that resolves a name in the
           problem's copy would otherwise meet the original field sorts beside
           a clause written over the substituted ones *)
        PCSP.Params.dtenv = dtenv_substituted;
        PCSP.Params.fenv = fenv_substituted;
      })
  @@
  let f (uni_senv, phi) =
    ( Map.Poly.map uni_senv ~f:(Term.subst_sorts_sort smap),
      Formula.subst_sorts smap phi )
  in
  match (targeted, fenv) with
  | true, Some fenv ->
      PCSP.Problem.map_old_where pcsp ~f
        ~touch:
          (clause_reaches_sort_key smap
             ~exi_senv:(PCSP.Problem.senv_of pcsp)
             ~fenv)
  | _ -> PCSP.Problem.map_old pcsp ~f

(* A digest of a preprocessed problem for [ParallelRace.Duplicate]: its
   formulas, each printed with every name that holds a digit (a fresh name
   such as [x16] or [#tvar42869], a sort parameter such as [a6]) renamed by
   first occurrence within it, sorted; then its sort, datatype and function
   environments and the process's function environment, renamed the same
   way.  The digest is one line per part: an MD5 of the environments, then
   one of each formula, sorted ([ParallelRace.Duplicate.covers] reads it).
   Two problems equal up to the fresh names the two sides drew get the same
   digest whatever order their name counters put the formulas in.  Equal
   digests of different problems would need two problems that differ only in
   which such names they use; the consequence is a dropped copy, never an
   answer. *)
module RaceDigest = struct
  let is_ident c = Char.is_alphanum c || String.mem "_#%'!" c

  let normalise_names s =
    let seen = Hashtbl.create (module String) in
    let buf = Buffer.create (String.length s) in
    let n = String.length s in
    let rec go i =
      if i < n then
        if is_ident s.[i] then (
          let j = ref i in
          while !j < n && is_ident s.[!j] do
            incr j
          done;
          let w = String.sub s ~pos:i ~len:(!j - i) in
          (if (not (Char.is_digit w.[0])) && String.exists w ~f:Char.is_digit
           then
             Buffer.add_string buf
               (sprintf "v%d"
                  (Hashtbl.find_or_add seen w ~default:(fun () ->
                       Hashtbl.length seen)))
           else Buffer.add_string buf w);
          go !j)
        else (
          Buffer.add_char buf s.[i];
          go (i + 1))
    in
    go 0;
    Buffer.contents buf

  let of_problem pcsp =
    let senv = PCSP.Problem.senv_of pcsp in
    let formulas =
      PCSP.Problem.formulas_of pcsp |> Set.to_list
      |> List.map ~f:(fun (uni_senv, phi) ->
             normalise_names
               (sprintf "[%d] %s" (Map.Poly.length uni_senv)
                  (Logic.ExtTerm.str_of_formula senv uni_senv phi)))
      |> List.sort ~compare:String.compare
    in
    let rest =
      normalise_names
        (String.concat ~sep:"\n"
           [
             str_of_sort_env_list Logic.ExtTerm.str_of_sort
               (Map.Poly.to_alist senv);
             DTEnv.str_of (PCSP.Problem.dtenv_of pcsp);
             FunEnv.str_of (PCSP.Problem.fenv_of pcsp);
             FunEnv.str_of (get_fenv ());
           ])
    in
    let text = String.concat ~sep:"\n" (rest :: formulas) in
    let line t = Md5.to_hex (Md5.digest_string t) in
    (* a diagnostic: with [COAR_RACE_DIGEST_DUMP=DIR], the text digested is
       written to DIR/<pid>.txt *)
    Option.iter (Sys.getenv "COAR_RACE_DIGEST_DUMP") ~f:(fun dir ->
        try
          Out_channel.write_all
            (Filename.concat dir
               (sprintf "%d.txt" (Pid.to_int (Core_unix.getpid ()))))
            ~data:text
        with exn when not (Common.Timer.is_async exn) -> ());
    String.concat ~sep:"\n"
      (line rest :: List.dedup_and_sort ~compare:String.compare
                      (List.map formulas ~f:line))
end

(* the nesting depth of [solve] in this process: a nested solve (a finite
   instance's, say) is not the problem a raced copy is compared on *)
let solve_depth = ref 0

(* An instrument: with COAR_SHARE_CENSUS set, the number of physically and of
   structurally distinct heap blocks of the problem's formulas (clauses, once
   clausal), on stderr at each point it is called with; set to
   [exit:<label>], the process exits at the point so labelled, so a
   preprocessing-only measurement stops there.  It decides nothing, and
   unset it does nothing.  Read at start-up, not through a [lazy], which two
   domains forcing at once would make raise. *)
let share_census_env = Stdlib.Sys.getenv_opt "COAR_SHARE_CENSUS"

let share_census label pcsp =
  match share_census_env with
  | None -> ()
  | Some v ->
      (match PCSP.Problem.clauses_of_opt ~full_clauses:false pcsp with
      | None ->
          let phis = PCSP.Problem.formulas_of ~full_clauses:false pcsp in
          Common.DagCensus.report ~items:(Set.length phis) label phis;
          let l = Set.to_list phis in
          Common.DagCensus.report ~items:(List.length l) (label ^ " [bodies]")
            (List.map l ~f:snd);
          Common.DagCensus.report ~items:(List.length l) (label ^ " [envs]")
            (List.map l ~f:fst)
      | Some cls -> Common.DagCensus.report ~items:(Set.length cls) label cls);
      if String.equal v ("exit:" ^ label) then Stdlib.exit 0

module Make (Config : Config.ConfigType) = struct
  let () =
    if Config.config.elim_subsume_hash_prefilter then
      Atomic.set PvarEliminator.ClauseSubsume.hash_prefilter true;
    if Config.config.elim_subsume_interned then
      Atomic.set PvarEliminator.ClauseSubsume.interned true;
    if Config.config.elim_subsume_persistent then
      Atomic.set PvarEliminator.ClauseSubsume.persistent true;
    if Config.config.elim_cnf_shared_fvs then
      Atomic.set PvarEliminator.cnf_shared_fvs true;
    if Config.config.elim_resolution_atom_pvs_memo then
      Atomic.set PvarEliminator.resolution_atom_pvs_memo true;
    if Config.config.elim_resolution_index then
      Atomic.set PvarEliminator.resolution_index true;
    if Config.config.pvar_elim_words_first then
      Atomic.set PvarEliminator.words_first true;
    if Config.config.pvar_elim_words_keep_proved then
      Atomic.set PvarEliminator.words_keep_proved true;
    if Config.config.matched_skip_spent_searches then
      PCSatCommon.SeqInstantiation.skip_spent_budget_searches := true;
    if Config.config.pvar_elim_defer_pure_to_verdict then
      Atomic.set PvarEliminator.defer_pure_to_verdict true;
    if Config.config.pvar_elim_defer_pure_to_round_end then
      Atomic.set PvarEliminator.defer_pure_to_round_end true;
    Option.iter Config.config.pvar_elim_words_full_major_every ~f:(fun n ->
        Atomic.set PvarEliminator.words_full_major_every (Some n));
    if Config.config.pvar_elim_implied_factor_equalities then
      Atomic.set PvarEliminator.implied_factor_equalities true;
    if Config.config.pvar_elim_split_int_binders_at_ite then (
      Atomic.set PvarEliminator.split_int_binders_at_ite true;
      (* with [verbose], one stderr line at exit tallying the questions
         rewritten: a diagnostic, so a plain run's output stays the answer *)
      if Config.config.verbose then IntBinderSplit.report_tallies ());
    if Config.config.elim_cnf_clause_tree then
      Atomic.set PvarEliminator.cnf_clause_tree true;
    if Config.config.shared_clause_dt_conversion then
      Atomic.set Clause.shared_dt_conversion true;
    if Config.config.share_term_conversions then
      Atomic.set Logic.ExtTerm.share_term_conversion true;
    if Config.config.share_rebuilt_formulas then (
      Atomic.set Logic.ExtTerm.share_term_conversion true;
      Atomic.set Logic.ExtTerm.share_term_conversion_terms true;
      Atomic.set Evaluator.share_simplify true;
      Atomic.set Normalizer.share_normalize true;
      Atomic.set PCSP.Problem.share_unused_params_fvs true);
    if Config.config.triv_fn_linear then
      Atomic.set PCSP.Problem.triv_fn_linear true;
    if Config.config.share_let_passes then
      Atomic.set LogicOld.share_let_passes true;
    if Option.is_some Config.config.resolution_max_growth then
      Atomic.set PvarEliminator.resolution_max_growth
        Config.config.resolution_max_growth;
    if Option.is_some Config.config.elim_set_aside_cnf_clauses then
      Atomic.set PvarEliminator.set_aside_cnf_clauses
        Config.config.elim_set_aside_cnf_clauses;
    if Config.config.elim_set_aside_definitional then
      Atomic.set PvarEliminator.set_aside_definitional true

  let config = Config.config
  let m = Debug.Config.(if config.verbose then enable else disable)

  module Debug = Debug.Make ((val m))

  module PvarEliminator =
    PvarEliminator.Make
      ((val m))
      (struct
        let resolution_threshold = config.resolution_threshold

        let resolution_complete_max_clauses =
          config.resolution_complete_max_clauses

        let resolution_complete_prebound = config.resolution_complete_prebound

        let resolution_complete_early_exit =
          config.resolution_complete_early_exit

        let resolution_complete_budget_ms = config.resolution_complete_budget_ms
        let propagate_lb_ub = config.propagate_lb_ub
        let condense_resolvents = config.condense_resolvents
        let condense_pure_resolvents = config.condense_pure_resolvents

        let condense_pure_unknown_free_resolvents =
          config.condense_pure_unknown_free_resolvents

        let condense_pure_max_checks = config.condense_pure_max_checks

        let condense_pure_shape_candidates =
          config.condense_pure_shape_candidates

        let condense_pure_shape_commutative =
          config.condense_pure_shape_commutative

        let condense_pure_inclusion_candidates =
          config.condense_pure_inclusion_candidates

        let condense_pure_max_search_nodes = config.condense_pure_max_search_nodes
        let condense_pure_memo_failures = config.condense_pure_memo_failures

        (* only ever turned on: the switch is process-wide *)
        let () =
          if config.elim_dedup_alpha_disjuncts then
            PvarEliminator.AlphaDedup.enabled := true

        let () =
          if config.elim_joint_condense then PvarEliminator.joint_condense := true;
          if config.elim_joint_prune_doomed then
            PvarEliminator.joint_prune_doomed := true
        let split_seq_reads = config.split_seq_reads
        let valid_timeout = config.pvar_elim_valid_timeout
        let valid_rlimit = config.pvar_elim_valid_rlimit
        let seq_axiom_rlimit = config.pvar_elim_seq_axiom_rlimit
        let valid_fresh_quantified = config.pvar_elim_valid_fresh_quantified
        let valid_memo = config.pvar_elim_valid_memo

        let valid_memo_reasks = config.pvar_elim_valid_memo_reasks

        let valid_memo_reask_timeout =
          config.pvar_elim_valid_memo_reask_timeout

        let valid_memo_reask_max_disjuncts =
          config.pvar_elim_valid_memo_reask_max_disjuncts

        let valid_warm_reask_ms = config.pvar_elim_valid_warm_reask_ms

        let valid_memo_alpha = config.pvar_elim_valid_memo_alpha

        let valid_defer_pure_min_disjuncts =
          config.pvar_elim_valid_defer_pure_min_disjuncts

        let seq_axiom_fallback_ms = config.pvar_elim_seq_axiom_fallback_ms
        let seq_axiom_fallback_once = config.pvar_elim_seq_axiom_fallback_once

        let seq_axiom_fallback_after_refusal_only =
          config.pvar_elim_seq_axiom_fallback_after_refusal_only

        let seq_axiom_fallback_charge_build =
          config.pvar_elim_seq_axiom_fallback_charge_build

        let split_seq_prefix_over_concat =
          config.pvar_elim_split_seq_prefix_over_concat

        let fork_refused_ms = config.pvar_elim_fork_refused_ms
        let cvc5_retry_ms = config.pvar_elim_cvc5_retry_ms
        let subsume_clauses = config.elim_subsume_clauses
        let tautology_test = config.elim_tautology_test
        let assign_before_cnf = config.elim_assign_before_cnf
      end)

  module DimReducer = DimReducer.Make ((val m))

  let simplify_clause ~id ~fenv ?(timeout = Some 20000) exi_senv (uni_senv, phi)
      =
    let simp =
      if config.simplification_with_smt then
        Z3Smt.Z3interface.simplify ~id fenv ~timeout
      else Fn.id
    in
    let ph = Common.PhaseTime.with_phase in
    let phi =
      ph "to-old" (fun () -> Logic.ExtTerm.to_old_fml exi_senv uni_senv phi)
      |> (fun phi -> ph "normalize" (fun () -> Normalizer.normalize phi))
      |> (fun phi -> ph "eval-simplify" (fun () -> Evaluator.simplify phi))
      |> (fun phi ->
      try simp phi with exn_ when not (Common.Timer.is_async exn_) -> phi)
      |> fun phi -> ph "of-old" (fun () -> Logic.ExtTerm.of_old_formula phi)
    in
    (*Out_channel.output_char Out_channel.stdout 'q';
      Out_channel.flush Out_channel.stdout;*)
    (* Debug.print @@ lazy ("[Preprocessor.simplify_clause] qelim"); *)
    let uni_senv, _, phi =
      ph "free-univ" (fun () ->
          Qelim.elim_free_univ_vars Map.Poly.empty exi_senv (uni_senv, [], phi))
    in
    (uni_senv, phi)

  let simplify ?(timeout = Some 20000) pcsp =
    let id = PCSP.Problem.id_of pcsp in
    let fenv = PCSP.Problem.fenv_of pcsp in
    if PCSP.Problem.is_cnf pcsp then pcsp
    else
      (* with [share_rebuilt_formulas], one scope of the normaliser's and the
         simplifier's memos for every clause, so the subformulas the clauses
         share are simplified once and stay shared (the same results) *)
      (if Atomic.get Logic.ExtTerm.share_term_conversion_terms then
         Logic.ExtTerm.with_shared_term_conversion
       else fun f -> f ())
      @@ fun () ->
      Normalizer.with_shared_normalize @@ fun () ->
      Evaluator.with_shared_simplify @@ fun () ->
      PCSP.Problem.map_if_raw pcsp
        ~f:
          (Set.Poly.map
             ~f:(simplify_clause ~id ~fenv ~timeout @@ PCSP.Problem.senv_of pcsp))

  (** obsolete *)
  let const_predicates ?(bpvs = Set.Poly.empty) exi_senv (uni_senv, phis) =
    let ppvs, npvs =
      let clauses =
        Set.Poly.map ~f:(fun (ps, ns, phi) -> (uni_senv, ps, ns, phi))
        @@ Formula.cnf_of (Logic.to_old_sort_env_map exi_senv)
        @@ Formula.and_of phis
      in
      let pvar_count, _ = ClauseSetOld.count_pvar_apps bpvs clauses in
      ( Set.Poly.filter_map pvar_count ~f:(fun (pvar, (_, _, nc)) ->
            if nc = 0 then Some pvar else None),
        Set.Poly.filter_map pvar_count ~f:(fun (pvar, (_, pc, _)) ->
            if pc = 0 then Some pvar else None) )
    in
    let atoms =
      Tuple2.uncurry Set.union @@ Formula.atoms_of @@ Formula.and_of phis
    in
    let const_map pvs value =
      Set.Poly.map pvs ~f:(fun pv ->
          match Set.find atoms ~f:(Atom.is_pvar_app_of pv) with
          | None -> assert false
          | Some pvar_app ->
              let pvar, sorts, _, _ = Atom.let_pvar_app pvar_app in
              ((pvar, sort_env_list_of_sorts sorts), value))
    in
    Set.union
      (const_map ppvs (Formula.mk_true ()))
      (const_map npvs (Formula.mk_false ()))

  let expand_bool_formula exi_senv (uni_senv, phi) =
    if Map.Poly.for_all uni_senv ~f:(Stdlib.( <> ) T_bool.SBool) then
      Set.Poly.singleton (uni_senv, phi)
    else
      (* assume that variables defined by uni_senv occur in phi*)
      let fvs =
        (*ToDo*)
        Formula.cnf_of (Logic.to_old_sort_env_map exi_senv) phi
        |> Set.concat_map ~f:(fun (_ps, _ns, phi) ->
            (*Set.union (Set.concat_map ~f:Atom.fvs_of @@ Set.union ps ns) @@*)
            Formula.fvs_of phi)
      in
      let bool_senv, other_senv =
        Map.Poly.partition_mapi uni_senv ~f:(fun ~key ~data ->
            if Stdlib.(data = T_bool.SBool) && Set.mem fvs key then First data
            else Second data)
      in
      let num_bool_vars = Map.Poly.length bool_senv in
      if 0 < num_bool_vars && num_bool_vars <= config.num_elim_bool_vars then
        Map.Poly.to_alist bool_senv
        |> List.power (fun (x, _) ->
            [ (x, T_bool.mk_true ()); (x, T_bool.mk_false ()) ])
        |> List.map ~f:(fun map ->
            (other_senv, Formula.subst (Map.Poly.of_alist_exn map) phi))
        |> Set.Poly.of_list
      else Set.Poly.singleton (uni_senv, phi)

  let expand_bool pcsp =
    (* [expand_bool_formula] can only fire when the number of Boolean
       variables is positive *and* within the configured budget, so a budget
       of zero makes the whole pass the identity.  Reaching that test is not
       free: it costs a CNF conversion per formula whose only use is to
       collect the free variables, and which is then thrown away, on top of a
       round trip through the other term representation.  Decide it here
       instead -- every shipped configuration sets the budget to zero. *)
    if config.num_elim_bool_vars <= 0 || PCSP.Problem.is_cnf pcsp then pcsp
    else
      PCSP.Problem.map_raw_old_exn pcsp
        ~f:(Set.concat_map ~f:(expand_bool_formula (PCSP.Problem.senv_of pcsp)))

  (* The solver's solution is over the signature the dimension reducer left
     (erased argument positions), while the definitions recorded by the
     eliminator were built before the reducer ran and apply the other
     predicates with their original arity.  The erased parameters must
     therefore be re-inserted into the solver's solution *before* the
     recorded definitions are closed under it; doing it afterwards
     substituted a 2-ary lambda into a 3-ary application and printed
     [((Leq 0 t) u)] as a definition (LinearArbitrary/01.c.small, found by
     [check_solution]).  The recorded
     definitions themselves never lose parameters (their predicates are gone
     before the reducer runs), so recovery on them is the identity. *)
  (* [extend]: whether the solution is completed with the definitions of the
     predicates preprocessing eliminated.  The verdict is the same either way
     and no solver is asked while completing it, but closing the recorded
     definitions into each other can build terms far larger than the problem
     (a minute and gigabytes on an input with a few hundred predicates
     resolved away), so a caller that reads only the verdict passes [false]
     and gets the solution of the predicates that were left. *)
  let solve_and_extend ?(extend = true) solver pcsp =
    let open Or_error in
    solver pcsp >>= fun (sol, info) ->
    let sol =
      match sol with
      | PCSP.Problem.Sat sol ->
          PCSP.Problem.Sat
            (PCSP.Problem.recover_elimed_params_of_sol
               (PCSP.Problem.args_record_of pcsp)
               sol)
      | sol -> sol
    in
    if not extend then return (sol, info)
    else
    Common.PhaseTime.with_phase "extend" @@ fun () ->
    return
      ( PCSP.Problem.extend_sol sol
          (* a predicate resolved away and afterwards unused has both a
             resolution definition and the default [remove_unused_params]
             records; the definition is the informative one *)
          (Map.Poly.merge
             (PCSP.Problem.sol_for_eliminated_of pcsp)
             (Map.Poly.map ~f:Lazy.force
                (PCSP.Problem.sol_for_resolved_of pcsp))
             ~f:(fun ~key:_ -> function
               | `Left v | `Right v -> Some v
               | `Both (_, resolved) -> Some resolved)),
        info )

  let recover_params_of_sol elimed_params_logs sol =
    let open Or_error in
    sol >>= fun (sol, info) ->
    let sol' =
      match sol with
      | PCSP.Problem.Sat sol ->
          PCSP.Problem.Sat
            (PCSP.Problem.recover_elimed_params_of_sol elimed_params_logs sol)
      | sol -> sol
    in
    return (sol', info)

  let print_pcsp = false

  (* Read over write for sequences, applied with the clause's own hypotheses.

     The law needs the READ index to be inside the sequence -- outside it both
     sides are underspecified and need not agree, so rewriting one into the
     other would claim an agreement the theory does not give.  That fact is
     almost always stated, but in the CLAUSE and not in the term, so the
     term-level simplifier declines every read whose sequence is a variable and
     the obligation reaches the solver with a write still under a read, which
     nothing decides: the sequence write is this repository's own symbol and no
     SMT solver has a law for it.  Here the clause is in hand, and a clause is a
     disjunction, so while rewriting one disjunct every other disjunct may be
     assumed false.

     The entailment is decided by a Z3 query on a quantifier-free formula with
     an explicit budget.  A clause with no read of a write is not queried at
     all, which is every clause of every problem that has no sequences. *)
  let rewrite_seq_reads ~id ~fenv ?(timeout = Some 1000) pcsp =
    (* The problem-level gate, and it is the one that has to be cheap: every
       problem reaches this pass, and mapping over the clauses converts each one
       between the two term representations and back.  A clause's sort
       environment is available WITHOUT that conversion, and a sequence the
       term-level rule cannot already handle is one that is a variable -- where
       the sequence is built by the syntax the length is computable from it and
       the rule fires on its own.  So a problem with no sequence-sorted clause
       variable is returned untouched, having paid a walk over sort environments
       and nothing else.  The sort is asked whether it MENTIONS a sequence, not
       whether it is one, so an array or a tuple of sequences still counts. *)
    let mentions_seq sort =
      Set.exists (Term.sorts_of_sort sort) ~f:(function
        | T_seq.SSeq _ -> true
        | _ -> false)
    in
    let some_seq_variable =
      Set.exists (PCSP.Problem.formulas_of pcsp) ~f:(fun (uni_senv, _) ->
          Map.Poly.exists uni_senv ~f:(fun sort ->
              mentions_seq @@ Logic.ExtTerm.to_old_sort sort))
    in
    if not some_seq_variable then pcsp
    else
      let has_read_of_write phi =
        (* one traversal: a clause with neither symbol is every clause of every
         problem that has no sequences, and it must not pay for this pass *)
        let fsyms = Formula.funsyms_of phi in
        Set.exists fsyms ~f:(function T_seq.SqNth _ -> true | _ -> false)
        && Set.exists fsyms ~f:(function T_seq.SqStore _ -> true | _ -> false)
      in
      let entails assumptions goal =
        match
          Z3Smt.Z3interface.check_valid ~timeout ~id fenv
            (Formula.mk_imply assumptions goal)
        with
        | `Valid -> true
        | _ -> false
      in
      PCSP.Problem.map_old pcsp ~f:(fun (uni_senv, phi) ->
          if not (has_read_of_write phi) then (uni_senv, phi)
          else (uni_senv, Evaluator.rewrite_seq_read_over_write ~entails phi))

  (* [match_private priv sub pat t] extends [sub] to a substitution for the
     variables in [priv] under which [pat] is syntactically [t]; every other
     variable, constant and sort must agree exactly.  Binders are not entered
     (the answer is then [None]), so the result is conservative: [Some] only
     when the instance relation really holds. *)
  let match_private priv sub pat t =
    let open Logic in
    let same a b = try Stdlib.(a = b) with Invalid_argument _ -> false in
    let rec go sub pat t =
      match (pat, t) with
      | Var (x, _), _ when Set.mem priv x -> (
          match Map.Poly.find sub x with
          | None -> Some (Map.Poly.set sub ~key:x ~data:t)
          | Some t' -> if same t' t then Some sub else None)
      | Var (x, _), Var (y, _) -> if Ident.tvar_equal x y then Some sub else None
      | Con (s1, _), Con (s2, _) -> if same s1 s2 then Some sub else None
      | App (f1, a1, _), App (f2, a2, _) ->
          Option.bind (go sub f1 f2) ~f:(fun sub -> go sub a1 a2)
      | TyApp (t1, s1, _), TyApp (t2, s2, _) ->
          if same s1 s2 then go sub t1 t2 else None
      | _ -> None
    in
    go sub pat t

  (* Drop, one at a time until none is left, a premise [n] of a clause for
     which some other premise [m] is an instance of [n] by a substitution for
     the variables of [n] that occur nowhere else in the clause and are not
     unknowns.  See [drop_implied_body_atoms] in the configuration for why
     the clause keeps its meaning.  Preserves: the head atoms, the pure part,
     and every premise that is not dropped; the sort environment loses only
     the variables that no longer occur. *)
  let drop_implied_body_atoms_of_clause exi_senv ((senv, ps, ns, phi) : Clause.t)
      : Clause.t =
    let rec loop ns =
      let found =
        Set.find_map ns ~f:(fun n ->
            let rest = Set.remove ns n in
            let others =
              Set.Poly.union_list
                [
                  Logic.Term.fvs_of phi;
                  Set.concat_map ps ~f:Logic.Term.fvs_of;
                  Set.concat_map rest ~f:Logic.Term.fvs_of;
                ]
            in
            let priv =
              Set.filter (Logic.Term.fvs_of n) ~f:(fun x ->
                  (not (Set.mem others x)) && not (Map.Poly.mem exi_senv x))
            in
            if Set.is_empty priv then None
            else if
              Set.exists rest ~f:(fun m ->
                  Option.is_some (match_private priv Map.Poly.empty n m))
            then Some n
            else None)
      in
      match found with Some n -> loop (Set.remove ns n) | None -> ns
    in
    let ns' = loop ns in
    if Set.length ns' = Set.length ns then (senv, ps, ns, phi)
    else
      let fvs = Clause.fvs_of (senv, ps, ns', phi) in
      Clause.canon
        (Map.Poly.filter_keys senv ~f:(Set.mem fvs), ps, ns', phi)

  (* Apply every equation between two integer variables of a clause as a
     renaming, then condense the clause ([ClauseOld.merge_int_var_equations],
     [ClauseOld.condense]: each an equivalence of the clause, so of the
     system).  A problem not in clausal form is
     returned as it is. *)
  let condense_final_clauses pcsp =
    match PCSP.Problem.clauses_of_opt ~full_clauses:false pcsp with
    | None -> pcsp
    | Some cls ->
        let exi_senv = PCSP.Problem.senv_of pcsp in
        let unknowns = Map.key_set exi_senv in
        PCSP.Problem.of_clauses ~params:(PCSP.Problem.params_of pcsp)
        @@ Set.Poly.map cls ~f:(fun cl ->
            let senv, ps, ns, phi = Clause.to_old_clause exi_senv cl in
            let ps', ns', phi' =
              ClauseOld.condense ~unknowns
              @@ ClauseOld.merge_int_var_equations ~unknowns (ps, ns, phi)
            in
            if
              Set.length ps' = Set.length ps
              && Set.length ns' = Set.length ns
              && Stdlib.(phi' == phi)
            then cl
            else
              let cl' = Clause.of_old_clause (senv, ps', ns', phi') in
              let fvs = Clause.fvs_of cl' in
              let senv', ps', ns', phi' = cl' in
              Clause.canon
                (Map.Poly.filter_keys senv' ~f:(Set.mem fvs), ps', ns', phi'))

  let drop_implied_body_atoms pcsp =
    match PCSP.Problem.clauses_of_opt ~full_clauses:false pcsp with
    | None -> pcsp
    | Some cls ->
        let exi_senv = PCSP.Problem.senv_of pcsp in
        PCSP.Problem.of_clauses ~params:(PCSP.Problem.params_of pcsp)
        @@ Set.Poly.map cls ~f:(drop_implied_body_atoms_of_clause exi_senv)

  (* Drop the arguments of ordinary unknowns that the clauses determine from
     the other arguments.

     For an unknown [P] with arguments [x_1 .. x_n], a PART of [x_i] is a term
     reached from it through the selectors of single-constructor datatypes (at
     most three deep), and a LEAF is a part where that walk stops (a sort that
     is not a single-constructor datatype, or the depth bound).  Every value
     [x_i] equals its constructor applied to its leaves, in every model, so
     [x_i] is fixed by its leaves.  The candidates are the equalities
     [l(x_i) = r(x_j)], [j <> i], between a leaf of one argument and a part of
     the same sort of another.  They are pruned to the largest subset [E] that
     is INDUCTIVE in the sense of Houdini (Flanagan and Leino, FME 2001): for
     every clause and every candidate unknown [P(a)] among its positive atoms,
       (the clause's constraint) /\ E(b) for each candidate atom [R(b)] among
       its negative atoms  ==>  E_P(a)
     is valid.  The other atoms of the clause are left out of the hypothesis,
     which only makes the question harder, so the result holds however they
     are solved.  An undecided question drops the candidate.

     Then an argument [x_i] all of whose leaves have an equality in [E_P] with
     an argument that is kept is dropped: [P] is replaced by a fresh unknown
     [Q] over the remaining arguments, with
       P := fun x. E_P(x) /\ Q(x without the dropped ones)
     recorded as [P]'s definition.

     Equisatisfiable.  The new problem is the old one with that definition
     substituted, so a solution of it gives one of the old problem.
     Conversely, if [sigma] solves the old problem then so does [sigma'],
     which conjoins [E_R] to each candidate [R]: a clause whose positive atom
     is [R(a)] gets [E_R(a)] from the inductiveness question, whose
     hypotheses [sigma'] now provides, and a clause whose negative atoms were
     strengthened is only weakened.  Under [E_P] the dropped argument equals
     the constructor term built from the kept arguments' parts, so
     [Q(y) := sigma'(P)(y with the dropped ones rebuilt)] satisfies
     [E_P(x) /\ Q(...) = sigma'(P)(x)], and the new problem is solved.  Both
     directions hold model by model, since each question was asked for
     validity; so a [sat] and a refutation of the new problem are each one of
     the old.

     Only unknowns of the ordinary kind, not in [bpvs] and never inside a
     clause's pure part are candidates.  The questions are asked of the
     problem's clause form; a problem with stable clauses is returned
     unchanged.  Returns the new problem and the
     new unknowns with their sorts.

     [budget_ms], when given, bounds the whole pass by a wall-clock deadline
     from its start: each question gets at most the time left, and once it is
     spent the problem is returned unchanged -- never a result built from an
     iteration that has not converged, whose candidates were proved inductive
     only against a larger set than the one it would keep.  [fallback_cap]
     caps the sequence-axiom fallback inside the pass's questions
     ([Z3interface.with_seq_axiom_fallback_cap]).  Neither can make the pass
     return anything but its full result or the unchanged problem.

     [syntactic_first] changes how each inductiveness question is answered,
     not which: a candidate is kept without a solver when the clause's
     definitions, selectors of their own constructors and the premise
     equalities (the clause's and the hypotheses') rewrite its two sides to
     the same term ([ClauseCone.Normal]); the others are asked as one
     conjunction, a countermodel dropping every candidate it falsifies by
     evaluation before the survivors are asked again, and one by one (each
     countermodel tried on the rest) when a countermodel drops nothing or the
     answer is undecided; and a head atom whose question reads the same
     candidate lists as when it was last asked (the lists only shrink, so
     equal lengths are equal lists) takes that answer again.  A syntactic
     proof is a proof of the whole question, a decided conjunction decides
     each candidate in it, and a countermodel of the premises falsifying a
     candidate refutes it, so wherever the solver decides the questions the
     kept set is the one the switch-off pass keeps; where the solver leaves a
     question undecided the switch can only keep more, each kept candidate
     proved.  [slice_questions] first asks the conjunction on the premises
     connected to the candidates' variables ([ClauseCone.slice]), whose proof
     proves the whole question. *)
  (* numbers the questions [COAR_SHARE_VALID_DUMP] keeps, over the process *)
  let share_dump_count = Atomic.make 0

  let rec share_determined_pvar_args ?(budget_ms = None) ?(fallback_cap = None)
      ?(syntactic_first = false) ?(slice_questions = false)
      ?(memo_questions = false) ~bpvs ~timeout pcsp =
    let unchanged = (pcsp, []) in
    let deadline =
      Option.map budget_ms ~f:(fun ms ->
          Common.Clock.now_s () +. (Float.of_int ms /. 1000.))
    in
    (* the time a question may still take, in ms: [timeout] under the
       deadline, or [Budget_spent] when nothing is left *)
    let question_timeout () =
      match deadline with
      | None -> timeout
      | Some d ->
          let left = Float.to_int ((d -. Common.Clock.now_s ()) *. 1000.) in
          if left <= 0 then raise Share_budget_spent
          else Some (match timeout with Some t -> Int.min t left | None -> left)
    in
    match
      Z3Smt.Z3interface.with_seq_axiom_fallback_cap fallback_cap @@ fun () ->
      share_determined_pvar_args_body ~question_timeout ~syntactic_first
        ~slice_questions ~memo_questions ~bpvs pcsp
    with
    | r -> r
    | exception Share_budget_spent ->
        Debug.print
        @@ lazy
             "[share_determined_pvar_args] budget spent: problem returned \
              unchanged";
        unchanged

  and share_determined_pvar_args_body ~question_timeout ~syntactic_first
      ~slice_questions ~memo_questions ~bpvs pcsp =
    let unchanged = (pcsp, []) in
    (* only an ordinary unknown of two or more arguments can have one; where
       none is left (every unknown eliminated, which is where a problem the
       zero-unknown verdict decides arrives) nothing is converted, so the pass
       is not only answer-preserving but inert *)
    let may_apply =
      let kind_map = PCSP.Problem.kind_map_of pcsp in
      Map.Poly.existsi (PCSP.Problem.senv_of pcsp) ~f:(fun ~key ~data ->
          (match Map.Poly.find kind_map key with
          | None | Some Kind.Ord -> true
          | _ -> false)
          && (not (Set.mem bpvs key))
          && List.length (Logic.Sort.args_of data) >= 2)
    in
    match
      if not may_apply then None
      else
        PCSP.Problem.clauses_of_opt ~full_clauses:false
          (PCSP.Problem.to_cnf pcsp)
    with
    | None -> unchanged
    | Some _
      when not
             (Set.is_empty (PCSP.Problem.params_of pcsp).PCSP.Params.stable_clauses)
      ->
        unchanged
    (* a problem already reduced to [false], or with no clause left, keeps its
       signature while no clause applies an unknown, so every candidate
       equality would be vacuously inductive and a definition made from it
       would constrain nothing; a refutation checker replaying that definition
       over the original signature was misled by it *)
    | Some cls when Set.for_all cls ~f:(fun c -> Set.is_empty (Clause.pvs_of c))
      ->
        unchanged
    | Some cls ->
        let id = PCSP.Problem.id_of pcsp in
        let fenv = PCSP.Problem.fenv_of pcsp in
        let exi_senv = PCSP.Problem.senv_of pcsp in
        let kind_map = PCSP.Problem.kind_map_of pcsp in
        let clauses =
          Clause.with_dt_scope @@ fun () ->
          List.map (Set.to_list cls) ~f:(Clause.to_old_clause exi_senv)
        in
        let in_pure =
          Set.Poly.union_list
          @@ List.map clauses ~f:(fun (_, _, _, phi) -> Formula.pvs_of phi)
        in
        (* the parts of a value of [sort], as selector paths, with the leaves
           marked *)
        let rec parts depth sort =
          match sort with
          | T_dt.SDT dt when depth > 0 -> (
              match Datatype.conses_of dt with
              | [ cons ] ->
                  ([], sort, false)
                  :: List.concat_map (Datatype.sels_of_cons cons) ~f:(fun sel ->
                         List.map
                           (parts (depth - 1) (Datatype.sort_of_sel dt sel))
                           ~f:(fun (path, s, leaf) ->
                             ((dt, Datatype.name_of_sel sel) :: path, s, leaf)))
              | _ -> [ ([], sort, true) ])
          | _ -> [ ([], sort, true) ]
        in
        let apply path t =
          List.fold path ~init:t ~f:(fun t (dt, name) -> T_dt.mk_sel dt name t)
        in
        let max_candidates = 64 in
        (* per unknown: its argument sorts and its candidate equalities
           (i, leaf path, j, part path) *)
        let candidates =
          Map.Poly.filter_mapi exi_senv ~f:(fun ~key ~data ->
              let pvar = Ident.tvar_to_pvar key in
              let ord =
                match Map.Poly.find kind_map key with
                | None | Some Kind.Ord -> true
                | _ -> false
              in
              if (not ord) || Set.mem bpvs key || Set.mem in_pure pvar then None
              else
                let sorts =
                  List.map ~f:Logic.ExtTerm.to_old_sort (Logic.Sort.args_of data)
                in
                if List.length sorts < 2 then None
                else
                  let ps = List.map sorts ~f:(parts 3) in
                  let cands =
                    List.concat_mapi ps ~f:(fun i pi ->
                        List.concat_map pi ~f:(fun (lp, ls, leaf) ->
                            if not leaf then []
                            else
                              List.concat_mapi ps ~f:(fun j pj ->
                                  if i = j then []
                                  else
                                    List.filter_map pj ~f:(fun (rp, rs, _) ->
                                        if
                                          String.equal (Term.str_of_sort ls)
                                            (Term.str_of_sort rs)
                                        then Some (i, lp, j, rp)
                                        else None))))
                  in
                  if List.is_empty cands then None
                  else Some (sorts, List.take cands max_candidates))
        in
        if Map.Poly.is_empty candidates then unchanged
        else
          let eq_of args (i, lp, j, rp) =
            Formula.eq (apply lp (List.nth_exn args i))
              (apply rp (List.nth_exn args j))
          in
          let pvar_args = function
            | Atom.App (Predicate.Var (Ident.Pvar name, _), args, _) ->
                Some (Ident.Tvar name, args)
            | _ -> None
          in
          let census = Census.on () in
          let questions = ref 0 in
          (* the answer to a validity question: [`Valid], [`Invalid m] with
             a countermodel [m], or [`Undecided] *)
          (* [memo_questions]: the answers given so far in this pass, keyed
             by the time limit and the simplified question *)
          let memo = Hashtbl.PolyDeep.create () in
          let rec ask ?(kind = "whole") phi =
            (* raises [Share_budget_spent] when the budget is gone, before any
               work on the question; never from inside the solver call *)
            let timeout = question_timeout () in
            let phi = Evaluator.simplify phi in
            if not memo_questions then ask_simplified ~kind ~timeout phi
            else
              match Hashtbl.find memo (timeout, phi) with
              | Some v ->
                  Atomic.incr share_memo_hits;
                  v
              | None ->
                  let v = ask_simplified ~kind ~timeout phi in
                  Hashtbl.set memo ~key:(timeout, phi) ~data:v;
                  v
          and ask_simplified ~kind ~timeout phi =
            incr questions;
            let t0 = if census then Common.Clock.now_s () else 0. in
            (* [COAR_SHARE_VALID_DUMP=dir] keeps each question as files in
               [dir] (a diagnostic; nothing is written without it) *)
            let v =
              Z3Smt.Z3interface.with_validity_dump
                ~var:"COAR_SHARE_VALID_DUMP" ~counter:share_dump_count ~id
                ~timeout:(Option.value timeout ~default:0)
                ~outcome:(function
                  | `Valid -> "valid"
                  | `Invalid _ -> "invalid"
                  | `Undecided -> "undecided")
                fenv phi
              @@ fun () ->
              if Z3Smt.Z3interface.may_not_return phi then `Undecided
              else
                match Z3Smt.Z3interface.check_valid ~timeout ~id fenv phi with
                | `Valid -> `Valid
                | `Invalid m -> `Invalid m
                | _ -> `Undecided
                | exception exn_ when not (Common.Timer.is_async exn_) ->
                    `Undecided
            in
            if census then
              Census.timed kind
                ~valid:(match v with `Valid -> true | _ -> false)
                (Common.Clock.now_s () -. t0);
            v
          in
          let valid ?kind phi =
            match ask ?kind phi with `Valid -> true | _ -> false
          in
          (* [true] only when the countermodel [m] of a question whose
             premises are the clause's makes [phi] false: every free variable
             of [phi] has a value in [m] (a variable the model leaves out may
             take any value, so it decides nothing), the values substituted
             simplify [phi] to [false], and [phi] has no symbol whose value the
             theory leaves open (a selector of a datatype with several
             constructors, a division, an uninterpreted function...), where
             the simplifier's value and the model's could differ.  Then [m]
             satisfies the premises and not [phi], so [premises => phi] is not
             valid: the solver, asked, could only answer [Invalid] or nothing,
             and either drops the candidate. *)
          let refutes m phi =
            (not (ClauseOld.interpretation_dependent phi))
            &&
            let vals =
              List.filter_map m ~f:(fun ((x, srt), v) ->
                  Option.map v ~f:(fun t -> (x, (Term.str_of_sort srt, t))))
            in
            let fvs = Formula.term_sort_env_of phi in
            let sub =
              Set.fold_until fvs ~init:Map.Poly.empty
                ~f:(fun sub (x, srt) ->
                  match
                    List.find vals ~f:(fun (y, (s, _)) ->
                        Ident.tvar_equal x y
                        && String.equal s (Term.str_of_sort srt))
                  with
                  | Some (_, (_, t)) -> Continue (Map.Poly.set sub ~key:x ~data:t)
                  | None -> Stop None)
                ~finish:Option.some
            in
            match sub with
            | None -> false
            | Some sub -> (
                try Formula.is_false (Evaluator.simplify (Formula.subst sub phi))
                with exn_ when not (Common.Timer.is_async exn_) -> false)
          in
          (* per clause, computed once: its premises as a list of conjuncts
             (the negated disjuncts of its pure part) *)
          let premises_of =
            let tbl = Hashtbl.Poly.create () in
            fun k phi ->
              Hashtbl.find_or_add tbl k ~default:(fun () ->
                  List.map (Formula.disjuncts_list_of phi) ~f:Formula.mk_neg)
          in
          let sides args (i, lp, j, rp) =
            (apply lp (List.nth_exn args i), apply rp (List.nth_exn args j))
          in
          let round = ref 0 in
          (* per (clause, head atom): the inputs of its last question (the
             body unknowns' candidate counts, the head's) and the candidates
             it kept *)
          let answered = Hashtbl.Poly.create () in
          let rec fix live =
            incr round;
            let st = Census.fresh () in
            let live' =
              List.foldi clauses ~init:live ~f:(fun k live (_, ps, ns, phi) ->
                  let hyp_pairs =
                    List.concat_map (Set.to_list ns) ~f:(fun atm ->
                        match pvar_args atm with
                        | Some (r, args) -> (
                            match Map.Poly.find live r with
                            | Some (_, cs) -> List.map cs ~f:(sides args)
                            | None -> [])
                        | None -> [])
                  in
                  let hyp_eqs =
                    List.map hyp_pairs ~f:(fun (l, r) -> Formula.eq l r)
                  in
                  let hyp = Formula.and_of (Formula.mk_neg phi :: hyp_eqs) in
                  (* what this clause's questions read of [live]: each body
                     unknown's candidate count.  The candidate lists only
                     shrink, by filtering, so equal counts are equal lists *)
                  let body_key =
                    List.filter_map (Set.to_list ns) ~f:(fun atm ->
                        Option.map (pvar_args atm) ~f:(fun (r, _) ->
                            ( r,
                              match Map.Poly.find live r with
                              | Some (_, cs) -> List.length cs
                              | None -> 0 )))
                  in
                  (* the syntactic normal form and the premise list, built
                     only when a question of this clause needs them *)
                  let nf = lazy (ClauseCone.Normal.make phi hyp_pairs) in
                  let premises = lazy (premises_of k phi @ hyp_eqs) in
                  let sliced goal =
                    Census.time "slice" (fun () ->
                        Formula.mk_imply
                          (Formula.and_of
                             (ClauseCone.slice (Lazy.force premises) goal))
                          goal)
                  in
                  List.foldi (Set.to_list ps) ~init:live ~f:(fun a live atm ->
                      match pvar_args atm with
                      | None -> live
                      | Some (p, args) -> (
                          match Map.Poly.find live p with
                          | None | Some (_, []) -> live
                          | Some (sorts, cs) -> (
                              match
                                if syntactic_first then
                                  match Hashtbl.find answered (k, a) with
                                  | Some (bk, n, cs')
                                    when Stdlib.(bk = body_key)
                                         && n = List.length cs ->
                                      Some cs'
                                  | _ -> None
                                else None
                              with
                              | Some cs' ->
                                  if census then Census.memo st;
                                  Map.Poly.set live ~key:p ~data:(sorts, cs')
                              | None ->
                              let live' =
                              let syn c =
                                let l, r = sides args c in
                                Census.time "syntax" (fun () ->
                                    ClauseCone.Normal.proves (Lazy.force nf) l r)
                              in
                              let synl =
                                if syntactic_first || census then
                                  List.map cs ~f:(fun c -> (c, syn c))
                                else List.map cs ~f:(fun c -> (c, false))
                              in
                              if census then (
                                let goal =
                                  Formula.and_of (List.map cs ~f:(eq_of args))
                                in
                                let all = Lazy.force premises in
                                let kept = ClauseCone.slice all goal in
                                let size ps =
                                  Formula.ast_size
                                    (Formula.mk_imply (Formula.and_of ps) goal)
                                in
                                Census.atom st ~whole_size:(size all)
                                  ~slice_size:(size kept)
                                  ~premises:(List.length all)
                                  ~kept:(List.length kept)
                                  ~cands:(List.length cs)
                                  ~syn:(List.count synl ~f:snd));
                              let goal_of cs =
                                Formula.and_of (List.map cs ~f:(eq_of args))
                              in
                              let whole c =
                                valid (Formula.mk_imply hyp (eq_of args c))
                              in
                              if not syntactic_first then
                                if
                                  valid ~kind:"whole-conj"
                                    (Formula.mk_imply hyp (goal_of cs))
                                then live
                                else
                                  let cs' = List.filter cs ~f:whole in
                                  Map.Poly.set live ~key:p ~data:(sorts, cs')
                              else
                                let residual =
                                  List.filter_map synl ~f:(fun (c, b) ->
                                      if b then None else Some c)
                                in
                                (* the countermodels found so far for this
                                   atom's questions, which all share the
                                   clause's premises and the hypotheses *)
                                let models = ref [] in
                                let refuted c =
                                  List.exists !models ~f:(fun m ->
                                      refutes m (eq_of args c))
                                in
                                let note = function
                                  | `Invalid m -> models := m :: !models
                                  | _ -> ()
                                in
                                (* the conjunction of the survivors, asked
                                   again while each countermodel refutes one
                                   of them: the candidates it refutes are not
                                   valid one by one either *)
                                let rec conj rs =
                                  if List.is_empty rs then []
                                  else
                                    match
                                      ask ~kind:"whole-conj"
                                        (Formula.mk_imply hyp (goal_of rs))
                                    with
                                    | `Valid -> rs
                                    | r -> (
                                        note r;
                                        let rs' =
                                          List.filter rs ~f:(fun c ->
                                              not (refuted c))
                                        in
                                        if census then
                                          Census.timed "model-drop" ~valid:false
                                            (Float.of_int
                                               (List.length rs
                                               - List.length rs'));
                                        match r with
                                        | `Invalid _
                                          when List.length rs' < List.length rs
                                          ->
                                            conj rs'
                                        | _ ->
                                            (* one by one, a countermodel of
                                               each question tried on the rest *)
                                            List.filter rs' ~f:(fun c ->
                                                (not (refuted c))
                                                &&
                                                match
                                                  ask (Formula.mk_imply hyp (eq_of args c))
                                                with
                                                | `Valid -> true
                                                | r ->
                                                    note r;
                                                    false))
                                in
                                let kept =
                                  if List.is_empty residual then []
                                  else if
                                    slice_questions
                                    && valid ~kind:"slice-conj"
                                         (sliced (goal_of residual))
                                  then residual
                                  else conj residual
                                in
                                let cs' =
                                  List.filter_map synl ~f:(fun (c, b) ->
                                      if b || List.mem kept c ~equal:phys_equal
                                      then Some c
                                      else None)
                                in
                                Map.Poly.set live ~key:p ~data:(sorts, cs')
                              in
                              (* the same question with the same inputs gets
                                 the same answer: remembered for the rounds
                                 that ask it again *)
                              if census then Census.progress ();
                              if syntactic_first then
                                Hashtbl.set answered ~key:(k, a)
                                  ~data:
                                    ( body_key,
                                      List.length cs,
                                      match Map.Poly.find live' p with
                                      | Some (_, cs') -> cs'
                                      | None -> cs );
                              live'))))
            in
            if census then Census.print_round st !round !questions;
            if
              Map.Poly.equal
                (fun (_, a) (_, b) -> List.length a = List.length b)
                live live'
            then live'
            else fix live'
          in
          let live = fix candidates in
          Debug.print
          @@ lazy
               (sprintf "[share_determined_pvar_args] %s"
                  (String.concat_map_list ~sep:"; " (Map.Poly.to_alist live)
                     ~f:(fun (p, (_, cs)) ->
                       sprintf "%s: %d of %d candidate equalities inductive"
                         (Ident.name_of_tvar p) (List.length cs)
                         (List.length (snd (Map.Poly.find_exn candidates p))))));
          (* the arguments to drop: in order, one whose every leaf is equal to
             a part of an argument that is kept *)
          let drops =
            Map.Poly.filter_map live ~f:(fun (sorts, cs) ->
                let n = List.length sorts in
                let dropped =
                  List.fold (List.range 0 n) ~init:Int.Set.empty ~f:(fun dropped i ->
                      let leaves =
                        List.filter_map (parts 3 (List.nth_exn sorts i))
                          ~f:(fun (lp, _, leaf) -> if leaf then Some lp else None)
                      in
                      let covered lp =
                        List.exists cs ~f:(fun (i', lp', j, _) ->
                            i' = i
                            && Stdlib.(lp' = lp)
                            && (not (Set.mem dropped j))
                            && j <> i)
                      in
                      if List.for_all leaves ~f:covered then Set.add dropped i
                      else dropped)
                in
                (* keep at least one argument *)
                if Set.is_empty dropped || Set.length dropped >= n then None
                else Some (sorts, cs, dropped))
          in
          if Map.Poly.is_empty drops then unchanged
          else
            let moves = ref [] in
            let defs, new_senv =
              Map.Poly.fold drops ~init:(Map.Poly.empty, [])
                ~f:(fun ~key:p ~data:(sorts, cs, dropped) (defs, senv) ->
                  let xs = List.map sorts ~f:(fun s -> (Ident.mk_fresh_tvar (), s)) in
                  let args = List.map xs ~f:(fun (x, s) -> Term.mk_var x s) in
                  let kept = List.filteri xs ~f:(fun i _ -> not (Set.mem dropped i)) in
                  let q =
                    Ident.mk_fresh_tvar
                      ~prefix:(Some (Ident.name_of_tvar p ^ "_shared"))
                      ()
                  in
                  let qsort =
                    Logic.Sort.mk_fun
                      (List.map kept ~f:(fun (_, s) -> Logic.ExtTerm.of_old_sort s)
                      @ [ Logic.BoolTerm.SBool ])
                  in
                  (* each equality once, whichever side it was found from *)
                  let e =
                    Formula.and_of
                    @@ List.filter_map cs ~f:(fun ((i, lp, j, rp) as c) ->
                           if
                             i > j
                             && List.exists cs ~f:(fun (i', lp', j', rp') ->
                                    i' = j && j' = i && Stdlib.(lp' = rp && rp' = lp))
                           then None
                           else Some (eq_of args c))
                  in
                  let def =
                    Logic.Term.mk_lambda (Logic.of_old_sort_env_list xs)
                    @@ Logic.BoolTerm.and_of
                         [
                           Logic.ExtTerm.of_old_formula e;
                           Logic.ExtTerm.mk_var_app q
                             (List.map kept ~f:(fun (x, _) -> Logic.ExtTerm.mk_var x));
                         ]
                  in
                  Debug.print
                  @@ lazy
                       (sprintf
                          "[share_determined_pvar_args] %s: arguments %s \
                           dropped, %s := %s"
                          (Ident.name_of_tvar p)
                          (String.concat_map_list ~sep:"," (Set.to_list dropped)
                             ~f:string_of_int)
                          (Ident.name_of_tvar p) (Formula.str_of e));
                  moves := (p, sorts, q, dropped) :: !moves;
                  (Map.Poly.set defs ~key:p ~data:def, (q, qsort) :: senv))
            in
            let pcsp' = PCSP.Problem.subst ~elim:true defs pcsp in
            let params = PCSP.Problem.params_of pcsp' in
            (* the declared candidate atoms of [p] go to [q], less those that
               mention a dropped argument *)
            let params =
              List.fold !moves ~init:params
                ~f:(fun params (p, sorts, q, dropped) ->
                  PCSP.Params.move_candidate_atoms params ~from:p ~sorts ~to_:q
                    ~keep:(fun i -> not (Set.mem dropped i)))
            in
            ( PCSP.Problem.update_params pcsp'
                {
                  params with
                  PCSP.Params.senv =
                    Map.force_merge params.PCSP.Params.senv
                      (Map.Poly.of_alist_exn new_senv);
                  kind_map =
                    Map.force_merge params.PCSP.Params.kind_map
                      (Map.Poly.of_alist_exn
                      @@ List.map new_senv ~f:(fun (q, _) -> (q, Kind.Ord)));
                  sol_for_eliminated =
                    Map.force_merge params.PCSP.Params.sol_for_eliminated defs;
                },
              new_senv )

  let preprocess ?(witness = WitnessConfig.default) ?(bpvs = Set.Poly.empty)
      ?(refute = true)
      ?(oracle = None) ?(normalize_params = false)
      ?(solver : (PCSP.Problem.t -> State.output Or_error.t) option = None)
      ?(finite_certificate = ref None) ?finite_race ?post_elim:post_elim_opt pcsp =
    (* the closure below would otherwise capture [pcsp] and keep the
       unnormalised problem reachable until preprocessing returns, although
       every step after [normalize] reads only its normal form (the binding is
       shadowed there): on a large input that is a second copy of the clause
       set held to the end. The body takes the problem out of the cell once,
       so the original is collectable as soon as [normalize] has returned *)
    let cell = ref (Some pcsp) in
    (* the steps below are timed as stages of one phase when the phase-time
       account is on, and nothing is done otherwise *)
    Common.PhaseTime.with_phase "preprocess" @@ fun () ->
    let pcsp = Option.value_exn !cell in
    cell := None;
    (* the unknowns the reader named quantified premises with are never eliminated: each
       stands for one premise so that a clause assuming several has one clause per premise
       conjunct instead of their product, and resolving one away would substitute the
       premise back and rebuild the product *)
    let bpvs =
      Set.union bpvs
        (PCSP.Parser.premise_unknowns_of (PCSP.Problem.senv_of pcsp))
    in
    let stage, _ = Common.PhaseTime.stages () in
    let stage name pcsp =
      share_census ("before " ^ name) pcsp;
      stage name
    in
    let orig_senv = PCSP.Problem.senv_of pcsp in
    Debug.print @@ lazy "**************** preprocessing  ****************";
    Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
    Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
    Debug.print @@ lazy "************************************************";
    let () = stage "normalize" pcsp in
    let pcsp = PCSP.Problem.normalize pcsp in
    share_census "after normalize" pcsp;
    Debug.print @@ lazy "normalized:";
    Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
    if print_pcsp then (
      Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
      Debug.print @@ lazy "");
    (* a single-valued predicate is solved as a domain predicate and a
       functional one; no-op without [Uniq] kinds *)
    let pcsp = PCSP.Problem.decompose_uniq pcsp in
    let pcsp = PCSP.Problem.to_nnf pcsp in
    let pcsp =
      if config.encode_head_disjunctions then
        PCSP.Problem.encode_head_disjunctions pcsp
      else pcsp
    in
    let pcsp =
      if config.instantiate_quantified_premises then
        PCSP.Problem.instantiate_quantified_premises pcsp
      else pcsp
    in
    Debug.print @@ lazy "NNF transformed:";
    Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
    if print_pcsp then (
      Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
      Debug.print @@ lazy "");
    if not config.enable then (
      let pcsp = PCSP.Problem.to_cnf pcsp in
      Debug.print @@ lazy "CNF transformed:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      Debug.print @@ lazy "************************************************";
      (* ToDo: the oracle is dropped rather than passed through here.
         Currently inert: [solve] only calls [preprocess] when [config.enable]
         is true, so this branch is unreachable from it, and every other caller
         (SPACER, MuStrat, Printer, RCaml, PCSat.Solver.preprocess) omits
         [~oracle] and discards the returned one. Passing it through would be a
         no-op until some caller both supplies and uses an oracle. *)
      (None, pcsp))
    else
      let () = stage "simplify" pcsp in
      let pcsp =
        Common.PhaseTime.with_phase "clauses" (fun () ->
            simplify ~timeout:(Some 1000) pcsp)
        |> fun pcsp ->
        share_census "after per-clause simplify" pcsp;
        Common.PhaseTime.with_phase "unused-params" (fun () ->
            PCSP.Problem.remove_unused_params pcsp)
      in
      Debug.print @@ lazy "simplified:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let () = stage "renormalize" pcsp in
      let pcsp = PCSP.Problem.normalize pcsp in
      Debug.print @@ lazy "normalized:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let () = stage "rewrite-seq-reads" pcsp in
      let pcsp =
        rewrite_seq_reads ~id:(PCSP.Problem.id_of pcsp)
          ~fenv:(PCSP.Problem.fenv_of pcsp)
          pcsp
      in
      Debug.print @@ lazy "sequence reads of writes rewritten:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      (* An existential over a sequence that its body reads only through the
         length is an arithmetic condition, and while it stands the clause is
         one nothing in reach decides: the validation query negates it into a
         universal over sequences, the solver answers neither way, and the loop
         then rejects every candidate without learning from it.  Replacing it is
         exact -- for a non-empty element sort every non-negative length is
         realised -- and it is what a ten-line satisfiable problem needed to be
         answered at all. *)
      let () = stage "rewrite-misc" pcsp in
      let pcsp =
        PCSP.Problem.map_old pcsp ~f:(fun (uni_senv, phi) ->
            (uni_senv, Evaluator.elim_seq_existentials phi))
      in
      Debug.print @@ lazy "sequence existentials over a length eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let pcsp =
        if config.split_single_cons_clause_vars && not (PCSP.Problem.is_cnf pcsp)
        then (
          let count = ref 0 in
          let pcsp =
            PCSP.Problem.map_old pcsp ~f:(fun (uni_senv, phi) ->
                let uni_senv, phi, n =
                  Evaluator.split_single_cons_free_vars
                    ~selected_only:config.split_single_cons_selected_only
                    uni_senv phi
                in
                count := !count + n;
                (uni_senv, phi))
          in
          Debug.print
          @@ lazy
               (sprintf "single-constructor clause variables split: %d" !count);
          if print_pcsp then (
            Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
            Debug.print @@ lazy "");
          pcsp)
        else pcsp
      in
      let () = stage "elim-unsat-kinds" pcsp in
      let pcsp =
        PCSP.Problem.(
          remove_unused_params
          @@ elim_unsat_wf_predicates ~print:Debug.print pcsp)
      in
      Debug.print @@ lazy "unsat wf predicates eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let pcsp =
        PCSP.Problem.(
          remove_unused_params
          @@ elim_unsat_nwf_predicates ~print:Debug.print pcsp)
      in
      Debug.print @@ lazy "unsat nwf predicates eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let pcsp =
        PCSP.Problem.(
          remove_unused_params
          @@ elim_unsat_parity_predicates ~print:Debug.print pcsp)
      in
      Debug.print @@ lazy "unsat parity predicates eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let pcsp =
        PCSP.Problem.(remove_unused_params @@ elim_triv_nwf_predicate pcsp)
      in
      Debug.print @@ lazy "trivial nwf predicates eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let pcsp =
        PCSP.Problem.(remove_unused_params @@ elim_triv_parity_predicate pcsp)
      in
      Debug.print @@ lazy "trivial parity predicates eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      (* The sweep of the clauses that mention no unknown
         ([PCSatCommon.UnknownFreeSweep]): each asked for validity at 500 ms,
         all within 5 s.  [Some p] when one is shown invalid, [p] being the
         problem as the single constraint [false]: no interpretation of the
         unknowns changes such a clause's truth value, so a model falsifying it
         is one in which the system has no solution.  [None] otherwise, the
         problem then going on as it was.  Its certificate is that bare leaf,
         which the checker reports as not re-derived. *)
      let sweep_unknown_free ~where pcsp =
        let senv = PCSP.Problem.senv_of pcsp in
        let formulas =
          List.map ~f:Evaluator.split_seq_reads_for_validity
          @@ PCSatCommon.UnknownFreeSweep.formulas_of_problem senv pcsp
        in
        let started = Common.Clock.now_s () in
        let result =
          PCSatCommon.UnknownFreeSweep.sweep
            ~pieces:(fun c -> [ c ])
            ~expired:(fun () ->
              Float.(Common.Clock.now_s () -. started > 5.))
            ~ask:(fun phi ->
              Z3Smt.Z3interface.check_valid ~timeout:(Some 500)
                ~fresh_solver:false ~id:(PCSP.Problem.id_of pcsp)
                (LogicOld.get_fenv ()) phi)
            formulas
        in
        Debug.print
        @@ lazy
             (sprintf
                "[unknown-free sweep] %s: %d clause(s) without an unknown: %s \
                 in %.2f s"
                where (List.length formulas)
                (match result with
                | Some (i, piece, _) ->
                    sprintf "clause %d refuted (%s)" i
                      (String.prefix (Formula.str_of piece) 400)
                | None -> "nothing refuted")
                (Common.Clock.now_s () -. started));
        match result with
        | None -> None
        | Some _ ->
            Some
              (PCSP.Problem.of_formulas ~params:(PCSP.Problem.params_of pcsp)
                 (Set.Poly.singleton
                    (Map.Poly.empty, Logic.BoolTerm.mk_bool false)))
      in
      (* The three passes below replace the problem by the constraint [false]
         when they refute it, which removes every unknown.  That is right for
         a caller asking whether the clauses are satisfiable, with or without
         [bpvs] (those keep unknowns whose solution is wanted, and an
         unsatisfiable problem has none).  It is wrong for a caller that only
         simplifies the clauses and reads unknowns back: the strategy
         refinement hands in a fragment whose strategy predicates are
         placeholders to be synthesised anew, and the fragment may be
         unsatisfiable as it stands (a fact [FN(x)] for every [x] beside a goal
         [not FN(2)]), so a refutation leaves nothing to read back.  Such a
         caller passes [~refute:false]. *)
      let may_refute = refute in
      (* set when a sweep refutes, so that neither the later sweep nor the
         finite instantiation is run on the constraint [false] it leaves *)
      let swept_refuted = ref false in
      let pcsp =
        if (not may_refute) || not config.sweep_unknown_free_clauses_before_elimination then pcsp
        else
          match sweep_unknown_free ~where:"before the elimination" pcsp with
          | None -> pcsp
          | Some refuted ->
              swept_refuted := true;
              refuted
      in
      Debug.print @@ lazy "*************** start elim pvars ***************";
      let () = stage "elim" pcsp in
      let param_logs =
        DimReducer.init_param_logs_of @@ PCSP.Problem.senv_of pcsp
      in
      PvarEliminator.Debug.set_id @@ PCSP.Problem.id_of pcsp;
      let ( ( sol_for_eliminated,
              elimination_reasons,
              sol_for_resolved,
              resolved_without_def ),
            pcsp ) =
        Z3Smt.Z3interface.with_seq_axiom_fallback_base
          config.pvar_elim_seq_axiom_fallback_budget_ms
        @@ fun () ->
        PvarEliminator.elim_pvs ~record_resolved_defs:witness.WitnessConfig.sat
          ~elim_one_sided_fn:config.elim_one_sided_fn_preds
          ~fn_consequences:config.add_fn_totality_consequences ~bpvs pcsp
      in
      (* Before [post_elim]: its encoding turns a clause that mentions no
         unknown into clauses over a fresh recursive unknown, and a clause
         that is simply invalid is then refuted only through the CEGIS loop
         building the unknown's chain, where the zero-unknown verdict would
         have found the countermodel by a few validity questions.  So the
         unknown-free clauses are swept first (same budgets and reading as
         the sweeps above), and a refutation stops the pass. *)
      let pcsp =
        match post_elim_opt with
        | None -> pcsp
        | Some post_elim -> (
            if (not may_refute) || !swept_refuted then post_elim pcsp
            else
              match
                sweep_unknown_free ~where:"before the post-elimination hook"
                  pcsp
              with
              | None -> post_elim pcsp
              | Some refuted ->
                  swept_refuted := true;
                  refuted)
      in
      (* an unknown the elimination introduced (or [post_elim] did) (the definitional clausal
         form of a formula set aside) has every argument still to reduce, as
         one of the input's has before the reduction looks at it *)
      let param_logs =
        Map.Poly.fold (PCSP.Problem.senv_of pcsp) ~init:param_logs
          ~f:(fun ~key ~data logs ->
            let pvar = Ident.tvar_to_pvar key in
            if Map.Poly.mem logs pvar then logs
            else
              let args = Logic.Sort.args_of data in
              Map.Poly.set logs ~key:pvar
                ~data:(Array.init (List.length args) ~f:(fun _ -> true), args))
      in
      let () = stage "post-elim" pcsp in
      let pcsp = PCSP.Problem.(remove_unused_params pcsp) in
      let pcsp =
        if config.cancel_seq_concat_equations then (
          let pcsp =
            PCSP.Problem.map_old pcsp ~f:(fun (uni_senv, phi) ->
                (uni_senv, Evaluator.cancel_seq_concat_equations phi))
          in
          Debug.print @@ lazy "common prefixes and suffixes of sequence equations cancelled:";
          Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
          pcsp)
        else pcsp
      in
      Debug.print @@ lazy "predicate variables eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      (* after the elimination, because that is what merges the clauses: a
         premise the specification states once per obligation arrives in the
         merged clause once per obligation, each copy with its own bound
         variable names, and nothing downstream recognises the copies as one *)
      let pcsp =
        if config.dedup_alpha_equivalent_disjuncts then
          PCSP.Problem.dedup_alpha_equivalent_disjuncts ~print:Debug.print pcsp
        else pcsp
      in
      (* the early duplicate check ([ParallelRace.Duplicate.early]): what
         follows up to the stage that shares determined arguments is
         refutation-only (the unknown-free sweep, the unfolding refutation,
         the finite instantiation), returning this problem unless it refutes
         it, so a raced copy whose problem here is the process's would ask the
         process's refutation questions again; only the outermost solve
         compares, as at the final check *)
      if !PCSatCommon.ParallelRace.Duplicate.early && !solve_depth = 1 then
        Common.PhaseTime.with_phase "race-digest-early" (fun () ->
            PCSatCommon.ParallelRace.Duplicate.checkpoint ~at:"e"
              ~log:(fun msg -> Debug.print @@ lazy ("[race] " ^ msg))
              (lazy (RaceDigest.of_problem pcsp)));
      (* A sort the input QUANTIFIES OVER -- a declare-forall-sort -- ranges
         over every non-empty type, so a solution must work for each of them and
         assuming one has at most n elements is an instance of that quantifier:
         a weakening, whose [unsat] transfers back while its [sat] says only
         that this size does not refute.  It is worth assuming because a proof
         by pigeonhole over the interpretations of a predicate on such a sort is
         infinite until the sort is finite, and finite it is a formula a solver
         decides.

         So: assert the whole clause set with the unknowns left uninterpreted --
         dropping their kinds only makes the system easier to satisfy, so an
         [unsat] still refutes -- together with "this sort has at most n
         elements", and try n upward.  The sizes matter: the input this was
         measured on is satisfiable at two and three elements and refuted at
         four, so a search that stops at the first [sat] answers nothing.

         A sort variable already reaches Z3 as an uninterpreted sort, so nothing
         is substituted; the bound is one extra conjunct.  This is deliberately
         a whole-problem check and not a per-clause one: an earlier attempt
         conjoined the same bound to one clause's refutation consequence, and it
         reached nothing at all because the clause it was written for is
         rejected before that query is built. *)
      let pcsp =
        if !swept_refuted then pcsp
        else if (not may_refute) || not config.sweep_unknown_free_clauses_before_finite_instances
        then pcsp
        else
          match sweep_unknown_free ~where:"before the finite instances" pcsp with
          | None -> pcsp
          | Some refuted ->
              swept_refuted := true;
              refuted
      in
      (* [stage_raced ~label ~enabled ~finite_race pcsp body]: [body ()] -- a
         refutation-only pass, which returns [pcsp] itself or a refuted
         problem -- computed here, or, when [enabled] and there is a place to
         leave the race, in a forked copy that answers only with a problem
         other than [pcsp] (a refutation) and then continues from here with it,
         while this process returns [pcsp] at once and records the race.
         Sequential when the copy cannot be forked, inside a solve bounded by a
         deadline, or on the substituting measurement route
         ([COAR_FINITE_EMIT]), which returns a problem other than [pcsp] that
         is not a refutation.  The races are left in [finite_race], which the
         caller finishes before its answer leaves. *)
      let stage_raced ~label ~enabled ~finite_race pcsp body =
        match finite_race with
        | Some races
          when enabled
               && (not (PCSatCommon.SolveDeadline.active ()))
               && Option.is_none (Stdlib.Sys.getenv_opt "COAR_FINITE_EMIT") -> (
            match
              Common.PhaseTime.with_phase (label ^ "-fork") (fun () ->
                  PCSatCommon.ParallelRace.start
                    ~report:(fun () ->
                      Common.PhaseTime.report
                        ~reason:(label ^ "-copy-answered"))
                    ~log:(fun msg ->
                      (* a line of the phase account, so only when it is on *)
                      if !Common.PhaseTime.on || !Common.PhaseTime.in_child
                      then (
                        prerr_endline
                          (sprintf "phase-time-race: at=%.3f %s: %s"
                             (Common.PhaseTime.now () -. Common.PhaseTime.t0)
                             label msg);
                        Out_channel.flush stderr))
                    (fun () ->
                      let pcsp' = body () in
                      if phys_equal pcsp' pcsp then None else Some pcsp'))
            with
            | `Won pcsp' -> pcsp'
            | `Racing t ->
                if String.equal label "finite-forall-sorts" then
                  Atomic.incr finite_races_started
                else Atomic.incr unfold_races_started;
                races := t :: !races;
                pcsp
            | `Not_started -> body ())
        | _ -> body ()
      in
      (* [refute_by_unfolding]: see [PCSatCommon.UnfoldRefute] for the
         procedure and why an [Invalid] resolvent refutes the problem.
         Refutation-only like the finite instantiation below, so with
         [refute_by_unfolding_parallel] it is raced the same way *)
      let pcsp =
        if (not may_refute) || (not config.refute_by_unfolding) || !swept_refuted then pcsp
        else
          stage_raced ~label:"refute-by-unfolding"
            ~enabled:config.refute_by_unfolding_parallel ~finite_race pcsp
          @@ fun () ->
          (* a problem not in clausal form is put in it here: the
             unfoldings read clauses, and the copy is discarded *)
          match
            PCSP.Problem.clauses_of_opt (PCSP.Problem.to_cnf pcsp)
          with
          | None -> pcsp
          | Some clauses ->
              let senv = PCSP.Problem.senv_of pcsp in
              (* COAR_UNFOLD_CENSUS set in the environment: the census of
                 [UnfoldRefute.GroundCensus] over the clauses this pass reads,
                 on stderr; set to [only], the process then exits, asking
                 nothing.  An instrument: it decides nothing. *)
              (match Stdlib.Sys.getenv_opt "COAR_UNFOLD_CENSUS" with
              | None -> ()
              | Some v ->
                  PCSatCommon.UnfoldRefute.GroundCensus.report
                    ~out:(fun s ->
                      Out_channel.output_string stderr ("unfold-census: " ^ s);
                      Out_channel.flush stderr)
                    ~label:"preprocessed" (Map.key_set senv)
                    (Set.to_list @@ ClauseSet.to_old_clause_set senv clauses);
                  if String.equal v "only" then Stdlib.exit 0);
              let started = Common.Clock.now_s () in
              (* each resolvent is asked in a forked copy killed at its three
                 questions' budget or at what is left of the pass's budget,
                 whichever is less: Z3's own timeout does not bound a question
                 over sequences, and [expired] is read only between
                 resolvents *)
              let dump_count = ref 0 in
              let ask_resolvent started phi =
                (* COAR_UNFOLD_DUMP=prefix in the environment: every solver
                   question of the [k]-th resolvent asked is written to
                   [prefix_k_j.smt2] ([Z3interface.with_query_dump]), so that a
                   refutation can be replayed and its countermodel read
                   outside the forked copy that found it.  An instrument: it
                   decides nothing. *)
                let dumped f =
                  match Stdlib.Sys.getenv_opt "COAR_UNFOLD_DUMP" with
                  | None -> f ()
                  | Some prefix ->
                      let k = !dump_count in
                      incr dump_count;
                      Z3Smt.Z3interface.with_query_dump
                        (sprintf "%s_%d" prefix k) f
                in
                dumped @@ fun () ->
                let left =
                  config.refute_by_unfolding_budget_ms
                  - Float.iround_down_exn
                      ((Common.Clock.now_s () -. started) *. 1000.)
                in
                PCSatCommon.UnfoldRefute.ask_forked ~print:Debug.print
                  ?step_ms:config.refute_by_unfolding_step_ms
                  ?guess_ms:config.refute_by_unfolding_guess_ms
                  ~hoist:config.refute_by_unfolding_hoist_bounds
                  ~ms:
                    (Int.max 1
                       (Int.min left (3 * config.refute_by_unfolding_timeout_ms)))
                  ~id:(PCSP.Problem.id_of pcsp) phi
              in
              let n, result =
                PCSatCommon.UnfoldRefute.refute ~print:Debug.print
                  ?max_size:config.refute_by_unfolding_max_size
                  ?counter_cap:config.refute_by_unfolding_counter_depth
                  ~solve_linear:config.refute_by_unfolding_solve_linear
                  ~linear:config.refute_by_unfolding_linear ~depth:config.refute_by_unfolding_depth ~max_copies:4096
                  ~expired:(fun () ->
                    Float.(
                      Common.Clock.now_s () -. started
                      > of_int config.refute_by_unfolding_budget_ms /. 1000.))
                  ~ask:(ask_resolvent started)
                  (Map.key_set senv)
                  (Set.to_list @@ ClauseSet.to_old_clause_set senv clauses)
              in
              Debug.print
              @@ lazy
                   (sprintf
                      "[unfold-refute] depth %d: %d goal resolvent(s): %s in \
                       %.2f s"
                      config.refute_by_unfolding_depth n
                      (match result with
                      | Some (i, _, _) -> sprintf "resolvent %d refuted" i
                      | None -> "nothing refuted")
                      (Common.Clock.now_s () -. started));
              let expired () =
                Float.(
                  Common.Clock.now_s () -. started
                  > of_int config.refute_by_unfolding_budget_ms /. 1000.)
              in
              let result =
                match result with
                | Some _ -> result
                | None
                  when config.refute_by_unfolding_fitting_doubling
                       && not (expired ()) ->
                    let n, result =
                      PCSatCommon.UnfoldRefute.refute_fitting
                        ~print:Debug.print
                        ?max_size:config.refute_by_unfolding_max_size
                        ~solve_linear:config.refute_by_unfolding_solve_linear
                        ~linear:false ~depth:config.refute_by_unfolding_depth
                        ~max_copies:4096 ~expired ~ask:(ask_resolvent started)
                        (Map.key_set senv)
                        (Set.to_list
                        @@ ClauseSet.to_old_clause_set senv clauses)
                    in
                    Debug.print
                    @@ lazy
                         (sprintf
                            "[unfold-refute] doubling, fitting levels: %d \
                             goal(s): %s in %.2f s"
                            n
                            (match result with
                            | Some (i, _, _) -> sprintf "goal %d refuted" i
                            | None -> "nothing refuted")
                            (Common.Clock.now_s () -. started));
                    result
                | None -> None
              in
              match result with
              | None -> pcsp
              | Some _ ->
                  swept_refuted := true;
                  PCSP.Problem.of_formulas ~params:(PCSP.Problem.params_of pcsp)
                    (Set.Poly.singleton
                       (Map.Poly.empty, Logic.BoolTerm.mk_bool false))
      in
      let () = stage "finite-forall-sorts" pcsp in
      let finite_stage_raced ~finite_race pcsp body =
        stage_raced ~label:"finite-forall-sorts"
          ~enabled:config.finite_forall_sorts_parallel ~finite_race pcsp body
      in
      let pcsp =
        let svars =
          Set.Poly.union_list @@ Set.to_list
          @@ Set.Poly.map ~f:(fun so ->
              LogicOld.Term.svs_of_sort @@ Logic.ExtTerm.to_old_sort so)
          @@ Set.Poly.of_list @@ Map.Poly.data @@ PCSP.Problem.senv_of pcsp
        in
        (* The sort variables some DATATYPE mentions.  A front end that
           monomorphises by NAME writes `(declare-datatypes ((D<a> 0)) ((par ()
           ((mk (fst a) (snd a))))))`, where `<a>` is part of the name and the
           fields are the variable itself, so the datatype has no parameters for a
           sort substitution to travel through. *)
        let dt_svars =
          List.fold ~init:Set.Poly.empty ~f:Set.union
          @@ List.concat_map
               (Map.Poly.data @@ LogicOld.get_dtenv ())
               ~f:(fun dt ->
                 List.concat_map (Datatype.conses_of dt) ~f:(fun cons ->
                     List.map
                       (Datatype.sorts_of_cons dt cons)
                       ~f:LogicOld.Term.svs_of_sort))
        in
        (* The third disjunct declines whenever a DATATYPE mentions one of the
           sort variables.  It was written because substitution reached a
           datatype through its PARAMETERS, and a front end that monomorphises
           by name writes one of arity zero whose selectors return the variable
           itself -- so the ordinary variables were replaced, the constructor
           was not, and the solver rejected the term outright.  That is fixed:
           an arity-zero datatype has its field sorts substituted directly, and
           the substituted datatype and function environments are swapped in
           whole with each query asked in a solver instance of its own, so the
           original and the copy, which share a name, never meet.  The decline
           is therefore no longer about correctness and the switch above turns
           it off.

           The switch above is on by default, so the decline is off: measured
           over 213 dependently quantified files, running the ladder on that
           family costs no verdict, no net answer and 1.02x. *)
        if
          (not config.finite_forall_sorts)
          || !swept_refuted
          || Set.is_empty svars
          || ((not config.finite_forall_sorts_by_name)
             && not (Set.are_disjoint dt_svars svars))
        then pcsp
        else
          finite_stage_raced ~finite_race pcsp @@ fun () ->
          (* universally closed over everything that is not an unknown.  A
             clause set is implicitly forall-closed, and [old_formula_of] only
             conjoins the clauses, so left as it comes the universal functions
             and the clause variables reach Z3 as free symbols -- which it reads
             existentially.  That is the wrong direction of strength: it asks
             whether SOME universal makes the clauses hold, where the system
             demands every one, and a query that weak refutes almost nothing. *)
          let phi =
            Common.PhaseTime.with_phase "finite-formula" @@ fun () ->
            let body = PCSP.Problem.old_formula_of pcsp in
            let unknowns = Map.key_set @@ PCSP.Problem.senv_of pcsp in
            let vars =
              Set.to_list
              @@ Set.filter (Formula.term_sort_env_of body) ~f:(fun (x, _) ->
                  not (Set.mem unknowns x))
            in
            Formula.mk_forall vars body
          in
          (* A route for measurement, off unless the environment asks for
             it by naming a size.  This pass decides the instance with ONE
             solver call, which is a decision procedure over a finite domain
             and stops deciding as soon as the domain has more than one
             element on some inputs -- one input here is decided in seconds at
             one element and undecided at 10, 60 and 300 seconds at two, while
             being only a sixth larger.  Whether a SEARCH over candidate
             solutions does better than a single call is a question about the
             constraint-solving loop rather than about this pass, and asking it
             needs the instance in the form that loop reads: a constraint
             problem, not a formula.  So with the variable set, the size it
             names is not decided but SUBSTITUTED INTO THE PROBLEM, which is
             then returned in place of the original for whatever the run was
             going to do with it -- print it, or solve it.

             The verdict contract is unchanged and is refutation-only, which is
             what makes this sound to read as an answer about the original
             system: no solution when a quantified sort has n elements means no
             solution at all, because a solution must work for every type,
             while a solution AT ONE SIZE concludes nothing about the others.
             So an [unsat] on the substituted problem transfers and a [sat]
             does not. *)
          let emit_size =
            Option.bind (Stdlib.Sys.getenv_opt "COAR_FINITE_EMIT") ~f:(fun s ->
                Common.Timer.try_with_sync (fun () -> Int.of_string s))
          in
          let emitted = ref None in
          (* the tree size of the problem before anything is substituted, the
             estimate [finite_forall_sorts_max_instance_size] is read against *)
          let problem_size = lazy (PCSP.Problem.ast_size_of pcsp) in
          let refuted_at n =
            match config.finite_forall_sorts_max_instance_size with
            | Some m
              when Option.is_none emit_size && Lazy.force problem_size * n > m
              ->
                finite_log (fun () ->
                    sprintf "size %d declined: estimate %d > %d" n
                      (Lazy.force problem_size * n) m);
                Debug.print
                @@ lazy
                     (sprintf
                        "size %d not built: the problem's tree size %d times \
                         %d exceeds %d"
                        n (Lazy.force problem_size) n m);
                `Undecided
            | _ ->
            finite_log (fun () ->
                sprintf "size %d estimate %d" n (Lazy.force problem_size * n));
            (* with [finite_forall_sorts_charge_construction], the query's
               budget is a deadline from here, read between the steps that
               build the instance *)
            let deadline =
              if config.finite_forall_sorts_charge_construction then
                Some
                  (Common.Clock.now_s ()
                  +. (Float.of_int config.finite_forall_sorts_query_timeout
                     /. 1000.))
              else None
            in
            let checkpoint () =
              match deadline with
              | Some d when Float.(Common.Clock.now_s () >= d) ->
                  raise Finite_construction_spent
              | _ -> ()
            in
            (* one set of constants per sort, SHARED between the bound and the
               expansion: the bound is what says the sort has no element outside
               them, and it says it of these.  Generated twice they would be
               unrelated, and instantiating a universal at constants nothing
               claims to cover proves nothing about it. *)
            (* SUBSTITUTE the sort; do not expand the quantifiers over it.  An
               earlier version replaced each quantifier over the sort by a copy
               of its body per element, and measured that reached 32,893,314
               characters at four elements, growing twentyfold per size -- no
               solver reads such a thing, and the same question written by hand
               at that size is twenty lines.  Declaring an n-constructor
               enumeration and leaving every quantifier where it stands hands
               the solver a finite domain to enumerate, which is what it is good
               at.  No cardinality axiom is needed with it: a datatype with n
               nullary constructors HAS n elements. *)
            let smap =
              Map.Poly.of_alist_exn
              @@ List.map (Set.to_list svars) ~f:(fun sv ->
                  let name =
                    PCSatCommon.CellQual.finite_sort_instance_name n
                      (Ident.name_of_svar sv)
                  in
                  let dt =
                    List.fold (List.init n ~f:Fn.id)
                      ~init:
                        (LogicOld.Datatype.make name
                           [ LogicOld.Datatype.mk_dt name [] ]
                           LogicOld.Datatype.FDt)
                      ~f:(fun dt i ->
                        LogicOld.Datatype.add_cons dt
                        @@ LogicOld.Datatype.mk_cons @@ sprintf "%s_%d" name i)
                  in
                  LogicOld.update_dtenv
                  @@ LogicOld.DTEnv.update_dt (LogicOld.get_dtenv ()) dt;
                  (sv, LogicOld.T_dt.SDT dt))
            in
            let bound = Formula.mk_true () in
            (* The substituted copies have to be in the datatype environment
               as well as in the formula: the conversion resolves a datatype it
               meets against that environment, and a copy that lives only inside
               the term is met as a sort the environment does not know, beside
               an original it does -- two definitions of one name, which the
               conversion rejects.  The environment is therefore substituted
               WHOLE and swapped in for everything below, so that every datatype in it
               is the substituted one and the names stay unique.  Registering
               the copies beside the originals instead needs them renamed, and
               renaming inside the substitution changes every generated
               identifier on every path that substitutes a sort, which moves
               CEGIS trajectories across the corpus for a case that has nothing
               to do with this pass. *)
            let saved_dtenv = LogicOld.get_dtenv () in
            (* The recursive functions the input declares -- the [SizeOf_…] of
               every datatype -- live in a process-global environment and are
               written over the ORIGINAL sorts.  The formula below has had the
               quantified sort substituted out of it, so handing the solver the
               environment as it stands offers the same function at two
               incompatible sorts and the query is rejected outright.  The
               environment is therefore substituted with the same map. *)
            let saved_fenv = LogicOld.get_fenv () in
            let dtenv_substituted, fenv_substituted =
              Common.PhaseTime.with_phase "finite-envs" (fun () ->
                  finite_instance_envs smap saved_dtenv saved_fenv)
            in
            (* The conversion resolves a function by name in the PROCESS-GLOBAL
               environment rather than in the one it is handed, so substituting
               the copy passed below changes nothing: a call whose sorts have
               been substituted still reaches a definition written over the
               original ones, and the solver rejects the pair as incompatible.
               The global environment is therefore swapped for the substituted
               one across this query and put back afterwards -- the query is
               synchronous.

               A BLIND overwrite of a process-global is safe only while this is
               the only solving call in the process, and it is not: a parallel
               fixpoint backend spawns a pool of domains, each of which reaches
               this pass, so two of them here would have one take the other's
               datatypes or restore the originals out from under it.  Merging
               instead is not available -- the pass wants the substituted
               definitions to REPLACE the originals, and merging two
               definitions of one name is the duplicate this module rejects --
               so the pass asks whether it is alone and concludes nothing when
               it is not.  Both substituted environments are built BEFORE the
               question is asked, so that nothing between taking the bracket
               and installing the restore can raise and strand it: a stranded
               bracket would silently disable this pass for the rest of the
               process. *)
            if not (LogicOld.try_enter_env_bracket ()) then (
              Debug.print
              @@ lazy
                   "another solving domain is holding the global datatype and \
                    function environments, so this size is left undecided \
                    rather than answered against environments that may not be \
                    ours";
              `Undecided)
            else (
            LogicOld.set_dtenv dtenv_substituted;
            LogicOld.set_fenv fenv_substituted;
            (* and put BOTH back on every exit, not only on the one that
               returns a verdict.  Everything between the swap and the answer
               can raise -- the simplification, the conversion, the solver, the
               alarm-based timer firing into whichever frame is running -- and a
               raise that skipped the restore would leave the rest of the run
               reading an environment in which one sort has been replaced by a
               finite enumeration.  Re-raising after restoring is what keeps the
               timeout a timeout. *)
            let restore () =
              LogicOld.set_fenv saved_fenv;
              LogicOld.set_dtenv saved_dtenv;
              LogicOld.leave_env_bracket ()
            in
            let protecting f =
              match f () with
              | v ->
                  restore ();
                  v
              | exception e ->
                  restore ();
                  raise e
            in
            (* everything from here to the answer runs with the substituted
               environments in place, which is why it is one function rather
               than a chain of bindings: the simplification that finishes the
               query formula reads the global datatype environment as much as
               the conversion does, and building the formula outside the swap
               expanded ORIGINAL definitions into an already-substituted
               formula -- two definitions of one name, arriving from two
               different stages *)
            let run_query () =
            (* The KINDS have to be asserted or the query answers the wrong
               question.  The clause set alone leaves each unknown an
               unconstrained predicate, and a functional one is then satisfied
               by [false] everywhere -- the same observation that closed the
               example-set route, a set of negative units having [false] as a
               model.  A solution of kind FN must be total and single-valued, so
               that is conjoined for each of them; leaving it out is what made
               this check report "no size refutes" on an input whose refutation
               at four elements had already been verified by hand. *)
            (* A FUNCTIONAL PREDICATE IS BETTER GIVEN AS A FUNCTION.  An
               [FN] unknown is the graph of a function, and stating that as a
               relation plus the axiom that it is total and single-valued asks a
               solver to search the relations and then discard the ones that are
               not graphs -- for an unknown with four arguments over a
               four-element sort and a four-bit universal that is 2^4096
               candidates where there are 4^1024 functions.  So each one becomes
               an uninterpreted function symbol and each of its atoms the
               equation saying what that function returns, which is exact
               because the axiom it replaces is what makes it so, and the axiom
               itself is then not needed at all. *)
            let fn_funs =
              Map.Poly.map (PCSP.Problem.fnpvs_senv_of pcsp) ~f:(fun so ->
                  let sorts =
                    List.map ~f:(fun s ->
                        Term.subst_sorts_sort smap
                        @@ Logic.ExtTerm.to_old_sort s)
                    @@ Logic.Sort.args_of so
                  in
                  ( Ident.mk_fresh_tvar ~prefix:(Some "#fnfun_") (),
                    List.drop_last_exn sorts,
                    List.last_exn sorts ))
            in
            let defunctionalise phi =
              Formula.map_atom phi ~f:(fun atom ->
                  match
                    if Atom.is_pvar_app atom then
                      let pvar, _, _, _ = Atom.let_pvar_app atom in
                      Map.Poly.find fn_funs (Ident.pvar_to_tvar pvar)
                    else None
                  with
                  | None -> Formula.mk_atom atom
                  | Some (f, sargs, sret) ->
                      let _, _, args, _ = Atom.let_pvar_app atom in
                      Formula.eq (List.last_exn args)
                      @@ Term.mk_fvar_app f sargs sret
                      @@ List.drop_last_exn args)
            in
            let expanded =
              (* THE ARRAYS OVER IT, TOO.  Making the quantified sort finite is
                 only half of a finite instantiation: a universal function over
                 it is an array-sorted variable, and a solver does not read the
                 array sort as finite just because its index sort is -- it will
                 not enumerate the 2^n boolean arrays over an n-element index,
                 so every quantifier over one stays a quantifier it can only
                 guess at.  Each such binder is therefore replaced by one binder
                 per element of the index sort, and the variable itself by the
                 array those n values build, which puts the whole query inside
                 what a finite model search can enumerate. *)
              (* AND AN INDEX SORT IS FINITE FOR MORE THAN ONE REASON.  The
                 enumeration this pass substitutes in is the obvious one, and
                 a front end that monomorphises by name wraps it: [Mut<a0>] is
                 a one-constructor record over the substituted sort and
                 [Option<a0>] a two-constructor one, so at size n they have n
                 and n+1 elements and a universal function indexed by either is
                 just as finite as one indexed by the enumeration itself.
                 Recognising only the enumeration left those arrays standing,
                 and Z3 then answered "incomplete (theory array)" on a goal
                 whose domain was finite throughout.  So the elements of an
                 index sort are enumerated structurally: a datatype all of whose
                 constructor arguments are themselves enumerable contributes the
                 product of its fields per constructor.

                 Two bounds keep this from being a trap.  A RECURSIVE datatype
                 has infinitely many elements and would be walked forever, so
                 the recursion is depth-bounded rather than cycle-detected --
                 the bound is what makes a list of unbounded length answer "not
                 enumerable" instead of diverging.  And the product grows with
                 the field count, so a domain past [max_elements] is declined:
                 the point of the expansion is to hand a solver something it can
                 enumerate, and past that size it is not. *)
              let max_elements = 16 in
              let max_depth = 3 in
              let rec elements_of_sort depth srt =
                if depth > max_depth then None
                else
                  match srt with
                  | LogicOld.T_dt.SDT dt ->
                      let per_cons c =
                        match
                          Option.all
                          @@ List.map
                               (LogicOld.Datatype.sorts_of_cons dt c)
                               ~f:(elements_of_sort (depth + 1))
                        with
                        | None -> None
                        | Some choices ->
                            (* the product is checked BEFORE it is built.  Each
                               field is already inside the bound, and a
                               constructor of three of them is not: building
                               first and measuring after is how this exhausted
                               the machine's memory on a datatype the bound was
                               meant to decline. *)
                            let size =
                              List.fold choices ~init:1 ~f:(fun acc elems ->
                                  if acc > max_elements then acc
                                  else acc * List.length elems)
                            in
                            if size > max_elements then None
                            else
                              let tuples =
                                List.fold_right choices ~init:[ [] ]
                                  ~f:(fun elems acc ->
                                    List.concat_map elems ~f:(fun e ->
                                        List.map acc ~f:(fun tl -> e :: tl)))
                              in
                              Some
                                (List.map tuples ~f:(fun args ->
                                     LogicOld.T_dt.mk_cons dt
                                       (LogicOld.Datatype.name_of_cons c)
                                       args))
                      in
                      Option.bind
                        (Option.all
                        @@ List.map (LogicOld.Datatype.conses_of dt) ~f:per_cons)
                        ~f:(fun lls ->
                          let es = List.concat lls in
                          if List.length es <= max_elements then Some es
                          else None)
                  | _ -> None
              in
              let elements_of = function
                | LogicOld.T_array.SArray (si, se) ->
                    Option.map (elements_of_sort 0 si) ~f:(fun es ->
                        (si, se, es))
                | _ -> None
              in
              let finitize_arrays phi =
                Formula.fold phi
                  ~f:
                    (object
                       method fatom atom = Formula.mk_atom atom
                       method fand p1 p2 = Formula.mk_and p1 p2
                       method for_ p1 p2 = Formula.mk_or p1 p2
                       method fnot p1 = Formula.mk_neg p1
                       method fimply p1 p2 = Formula.mk_imply p1 p2
                       method fiff p1 p2 = Formula.mk_iff p1 p2
                       method fxor p1 p2 = Formula.mk_xor p1 p2
                       method fletrec funcs p1 = Formula.mk_letrec funcs p1

                       method flet var sort def body =
                         Formula.mk_let_formula var sort def body

                       method fbind binder senv p1 =
                         let senv', sub =
                           List.fold senv ~init:([], Map.Poly.empty)
                             ~f:(fun (acc, sub) (x, so) ->
                               match elements_of so with
                               | None -> (acc @ [ (x, so) ], sub)
                               | Some (si, se, elems) ->
                                   let ys =
                                     List.map elems ~f:(fun _ ->
                                         Ident.mk_fresh_tvar
                                           ~prefix:(Some "#at_") ())
                                   in
                                   let arr =
                                     List.fold2_exn (List.tl_exn elems)
                                       (List.tl_exn ys)
                                       ~init:
                                         (LogicOld.T_array.mk_const_array si se
                                         @@ Term.mk_var (List.hd_exn ys) se)
                                       ~f:(fun a e y ->
                                         LogicOld.T_array.mk_store si se a e
                                         @@ Term.mk_var y se)
                                   in
                                   ( acc @ List.map ys ~f:(fun y -> (y, se)),
                                     Map.Poly.set sub ~key:x ~data:arr ))
                         in
                         Formula.mk_bind binder senv' @@ Formula.subst sub p1
                    end)
              in
              (* AND THE UNKNOWNS' ARRAY ARGUMENTS WITH THEM.  Expanding the
                 quantified arrays is still not enough on its own: an unknown
                 declared over a universal function keeps an argument of array
                 sort, so a solver has to invent a predicate on arrays, and it
                 will not enumerate those even when their index sort has four
                 elements -- measured, the query is undecided at a 60 s budget
                 at a size where the same problem written by hand answers at
                 once.  Each such argument position is therefore replaced by one
                 argument per element of the index sort, holding what the array
                 reads there, which leaves every sort in the query finite. *)
              let finitize_pvar_args phi =
                Formula.map_atom phi ~f:(fun atom ->
                    if not (Atom.is_pvar_app atom) then Formula.mk_atom atom
                    else
                      let pvar, sorts, args, info = Atom.let_pvar_app atom in
                      let sorts', args' =
                        List.unzip
                        @@ List.map2_exn sorts args ~f:(fun so t ->
                            match elements_of so with
                            | None -> ([ so ], [ t ])
                            | Some (si, se, elems) ->
                                ( List.map elems ~f:(fun _ -> se),
                                  List.map elems ~f:(fun e ->
                                      LogicOld.T_array.mk_select si se t e) ))
                      in
                      Formula.mk_atom
                      @@ Atom.mk_pvar_app ~info pvar (List.concat sorts')
                           (List.concat args'))
              in
              (* AND THEN NO ARRAY AT ALL.  What the two rewrites above leave
                 is a read of a rebuilt array at a variable index, which the
                 solver can only decide through the theory of arrays -- the same
                 problem in a smaller form, and measured it is where the last
                 two sizes still go unanswered.  Over an index sort with n
                 elements a read is a case split on which element the index is,
                 so each one is written out as that split and the array
                 disappears from the query along with the theory. *)
              let eliminate_selects phi =
                Formula.map_term phi ~f:(fun t ->
                    match t with
                    | Term.FunApp
                        (LogicOld.T_array.ASelect (si, se), [ a; i ], _) -> (
                        match
                          elements_of (LogicOld.T_array.SArray (si, se))
                        with
                        | None -> t
                        | Some (_, _, elems) ->
                            let read e = LogicOld.T_array.mk_select si se a e in
                            List.fold_right
                              (List.tl_exn @@ List.rev elems)
                              ~init:(read @@ List.last_exn elems)
                              ~f:(fun e acc ->
                                T_bool.mk_if_then_else
                                  (T_bool.of_formula @@ Formula.eq i e)
                                  (read e) acc))
                    | _ -> t)
              in
              (* and the same for the function symbols the step above
                 introduced, whose arguments are the unknown's arguments and so
                 include the same arrays *)
              let finitize_fun_args phi =
                Formula.map_term phi ~f:(fun t ->
                    match t with
                    | Term.FunApp (FVar (f, sargs, sret), args, info) ->
                        let sargs', args' =
                          List.unzip
                          @@ List.map2_exn sargs args ~f:(fun so a ->
                              match elements_of so with
                              | None -> ([ so ], [ a ])
                              | Some (si, se, elems) ->
                                  ( List.map elems ~f:(fun _ -> se),
                                    List.map elems ~f:(fun e ->
                                        LogicOld.T_array.mk_select si se a e) ))
                        in
                        Term.mk_fvar_app ~info f (List.concat sargs') sret
                          (List.concat args')
                    | _ -> t)
              in
              (* ONE PASS IS NOT ENOUGH WHEN THE FUNCTIONS ARE CURRIED.  A
                 universal function of two arguments is an array whose VALUE
                 sort is another array, so replacing a binder over it by one
                 binder per element of its index leaves binders that are still
                 arrays -- and an argument position expanded by reading at each
                 element yields terms that are still arrays.  Each round strips
                 one level, so the chain is repeated until the formula stops
                 changing, which is the arity of the deepest universal function
                 and is a handful.  Left at one round this reported 24 array
                 reads surviving and the solver answered "incomplete (theory
                 array)" on a domain that was finite throughout. *)
              let step phi =
                let phi = finitize_arrays phi in
                checkpoint ();
                let phi = eliminate_selects phi in
                checkpoint ();
                let phi = finitize_pvar_args phi in
                checkpoint ();
                finitize_fun_args phi
              in
              (* Each round is simplified before the next.  A round rewrites
                 a read at a variable index into a case split whose branches
                 are reads of the same rebuilt array at each element, so an
                 unsimplified chain of rounds copies every array once per
                 element per level of currying; simplifying reduces those reads
                 of a rebuilt array at a ground element to the element's value
                 at once.  Measured on a dependently quantified input at two
                 elements: the finished instance is the same 103,487
                 characters either way, but building it took 27.5 s and more
                 than 3.5 GB unsimplified (out of memory under a 4 GB limit,
                 in the textual comparison below) and 0.3 s simplified.
                 Simplification preserves meaning, so the instance is the
                 same question. *)
              let rec loop n phi =
                if n <= 0 then phi
                else
                  let phi' = step phi in
                  checkpoint ();
                  let phi' = Evaluator.simplify phi' in
                  checkpoint ();
                  if String.equal (Formula.str_of phi') (Formula.str_of phi)
                  then phi
                  else loop (n - 1) phi'
              in
              Common.PhaseTime.with_phase "finite-query-build" @@ fun () ->
              let phi = Formula.subst_sorts smap phi in
              checkpoint ();
              let phi = defunctionalise phi in
              checkpoint ();
              let phi = loop 5 phi in
              let phi = Evaluator.simplify phi in
              checkpoint ();
              phi
            in
            (* The instance is printed once and truncated.  Its text is a tree
               while the formula is a graph whose subterms are shared, so the
               text can be exponentially larger than the value: a verbose run
               that printed it whole, and measured it three more times, ran
               out of memory at two elements on an input whose size-one
               instance is 91,000 characters. *)
            Debug.print
            @@ lazy
                 (let text = Formula.str_of expanded in
                  let shown = 4000 in
                  sprintf
                    "size %d: %d characters, %d quantifiers, %d select(s)\n\
                     %s\n\
                     %s%s"
                    n (String.length text)
                    (List.length
                    @@ String.substr_index_all ~may_overlap:false
                         ~pattern:"forall" text)
                    (List.length
                    @@ String.substr_index_all ~may_overlap:false ~pattern:"["
                         text)
                    (String.concat ~sep:" "
                    @@ List.map (Map.Poly.data smap) ~f:(function
                      | LogicOld.T_dt.SDT dt ->
                          sprintf "%s has %d constructor(s)"
                            (LogicOld.Datatype.name_of dt)
                            (List.length @@ LogicOld.Datatype.conses_of dt)
                      | _ -> "not a datatype"))
                    (String.prefix text shown)
                    (if String.length text > shown then " ..." else ""));
            (* A FRESH solver instance, because a pooled one ACCUMULATES its
               declarations: the entry point below passes the instance's
               existing datatype and function environments as the [init] of the
               new ones, and a datatype already declared there under a given
               name is reused rather than redeclared.  This query hands the
               solver the same datatype NAMES with substituted field sorts, so
               an instance that has already seen the originals declares the
               constructor at the original argument sorts and then rejects the
               substituted term outright -- "Sort mismatch at argument #1 for
               function (declare-fun Option.Some<a1> (|#svar_a1|) ...)".  The
               instance pool is keyed by the id, so an id nothing else uses is
               an instance whose environments start empty.  Each size needs its
               own, the sizes differing in exactly those datatypes. *)
            let query_id =
              incr fresh_finite_query_id;
              Some !fresh_finite_query_id
            in
              let ask () =
              Z3Smt.Z3interface.check_sat
                ~timeout:
                  (Some
                     (match deadline with
                     | None -> config.finite_forall_sorts_query_timeout
                     | Some d ->
                         let left =
                           Float.to_int
                             ((d -. Common.Clock.now_s ()) *. 1000.)
                         in
                         if left <= 0 then raise Finite_construction_spent
                         else
                           Int.min config.finite_forall_sorts_query_timeout left))
                ~id:query_id
                fenv_substituted
                [ Formula.mk_and bound expanded ]
              in
              let query = Formula.mk_and bound expanded in
              if
                config.finite_forall_sorts_fork_query
                && Z3Smt.Z3interface.may_not_return query
              then
                (* the kill is the budget: the solver's own timer is the one
                   that does not hold here *)
                let ms = config.finite_forall_sorts_query_timeout in
                match
                  PCSatCommon.ForkedQuery.run ~ms (fun () ->
                      match ask () with
                      | `Unsat -> `U
                      | `Sat _ -> `S
                      | `Unknown r -> `K r
                      | `Timeout -> `T)
                with
                | Some `U -> `Unsat
                | Some `S -> `Sat []
                | Some (`K r) -> `Unknown r
                | Some `T | None -> `Timeout
              else ask ()
              (* end of [run_query]: everything from the kinds to the answer.
                 Its body is left at the surrounding indentation rather than
                 nested, because it is several hundred lines and re-indenting
                 them would bury the change in whitespace. *)
            in
            (* THE INSTANCE AS A PROBLEM rather than as a query.  Two routes
               want it: the measurement route below, which returns it in place
               of the original, and the nested solve further down, which asks a
               search to refute what one solver call could not.  Everything a
               sort lives in has to be substituted, and the list is longer than
               it looks -- the clauses, the unknowns' argument sorts, and the
               datatype and function environments the PROBLEM carries beside
               the process-global ones, since a consumer that resolves a name
               in that copy meets the original field sorts next to a clause
               written over the substituted ones. *)
            let substituted_problem () =
              Common.PhaseTime.with_phase "finite-instance" (fun () ->
                  finite_instance_problem
                    ~targeted:config.finite_forall_sorts_targeted_instance
                    ~fenv:saved_fenv smap ~dtenv_substituted
                    ~fenv_substituted pcsp)
            in
            (* and every pooled solver instance has to go with it.  An
               instance keeps the declarations it has already made, and the
               stages above this one have declared the datatypes under their
               ORIGINAL field sorts; the substituted problem uses the same
               datatype names, so the first term built over it is rejected
               against a constructor declared at the old argument sort.
               Dropping the pool makes the next query declare them afresh from
               the substituted environment -- and it has to be dropped AFTER a
               nested solve too, or the outer run inherits instances holding
               the substituted declarations. *)
            if Option.exists emit_size ~f:(fun m -> m = n) then (
              (* and NOT under [protecting]: the substituted datatype and
                 function environments are process-global and everything
                 downstream -- the printer, the solver -- resolves a datatype
                 and a recursive function by name in them, so restoring the
                 originals here would hand the next stage a problem whose sorts
                 no environment defines.  The run is a measurement that ends
                 with this problem; it does not go back to the original one. *)
              emitted := Some (substituted_problem ());
              Z3Smt.Z3interface.clear_instance_pool ();
              `Undecided)
            else
            let t_query = Common.Clock.now_s () in
            let ans =
              Common.PhaseTime.with_phase "finite-query" @@ fun () ->
              protecting (fun () ->
                  try run_query ()
                  with Finite_construction_spent ->
                    finite_log (fun () ->
                        sprintf "size %d construction past its budget" n);
                    `Timeout)
            in
            finite_log (fun () ->
                sprintf "size %d query %s %.2f s" n
                  (match ans with
                  | `Unsat -> "unsat"
                  | `Sat _ -> "sat"
                  | `Unknown _ -> "unknown"
                  | `Timeout -> "timeout")
                  (Common.Clock.now_s () -. t_query));
            (* which of the two it is decides whether anything more is worth
               trying here: a solver that answers "satisfiable" at this size
               has decided the question and the hand argument has to be
               re-examined, while one that gives up has only run out of budget,
               which is a different problem with different remedies. *)
            Debug.print
            @@ lazy
                 (sprintf "size %d answered %s" n
                    (match ans with
                    | `Unsat -> "unsat"
                    | `Sat _ -> "sat"
                    | `Unknown reason -> "unknown: " ^ reason
                    | `Timeout -> "timeout"));
            match ans with
            | `Unsat -> `Refuted
            | `Sat _ -> `Decided
            | _ when not config.finite_forall_sorts_nested_solve -> `Undecided
            (* no solver to hand the instance to (the printer, a property test):
               decided before the bracket below is taken, since that branch
               returns without releasing it, and a stranded bracket would
               decline this pass for the rest of the process *)
            | _ when Option.is_none solver -> `Undecided
            (* The single query above has finished and its restore has released
               the bracket, so the nested solve -- which swaps the environments
               again, and for far longer, a whole solving run rather than one
               call -- has to ask for it on its own behalf.  Declining here
               leaves the size undecided, which is what the caller already does
               when the nested solve is switched off. *)
            | _ when not (LogicOld.try_enter_env_bracket ()) -> `Undecided
            | _ -> (
                (* THE QUERY GAVE UP; THE SEARCH MAY NOT.  What this pass asks
                   at each size is whether some interpretation of the unknowns
                   satisfies the instantiated clauses -- unknowns that are
                   PREDICATES, which makes it a constraint-solving problem
                   handed to a single solver call by the tool that exists to
                   solve constraint-solving problems.  Measured on one
                   dependently quantified input at two elements, the call is
                   undecided at 10, 60 and 300 seconds while a search over
                   candidate solutions refutes the same instance in two rounds
                   and seven seconds.  So an undecided query is evidence about
                   the call and not about the instance, and the instance is
                   worth handing to the loop.

                   ONLY A REFUTATION TRANSFERS, which is the contract this pass
                   already has: a solution must work for every non-empty type,
                   so no solution at one cardinality means none at all, while a
                   solution AT one cardinality says nothing about the others.
                   Anything but [Unsat] is therefore discarded and the original
                   problem continues.

                   The recursion is one level deep BY CONSTRUCTION and needs no
                   depth counter: the nested solve runs its own preprocessing,
                   which reaches this pass again with a problem whose quantified
                   sorts have all been substituted away, and the guard on the
                   sort variables of the unknowns' sorts then declines it on
                   entry. *)
                match solver with
                | None -> `Undecided
                | Some solve_instance ->
                    (* The environments must be in place before the nested
                       solve begins and restored only after it has finished,
                       which is what the swap below brackets; it is not a place
                       to move the restore earlier.  The reason is not that the
                       nested solve runs in parallel -- this constraint solver
                       spawns no domains of its own -- but that it runs a whole
                       solving pipeline, which reads the datatype and function
                       environments at every stage, from its own preprocessing
                       down to each conversion of a term for the solver.
                       Restoring at the point the substituted problem is built
                       would hand the pipeline the ORIGINAL datatypes to
                       interpret terms written over the substituted ones.

                       The blind [set_] rather than the retrying [update_] is
                       safe only while no other thread of this process is
                       solving, which holds for every configuration this has
                       been measured under: the callers that spawn domains do
                       so AROUND a constraint-solving call and not inside one.
                       A caller that ran two such calls at once, each reaching
                       this pass, would have one overwrite the other's
                       environment silently. *)
                    let saved_dtenv' = LogicOld.get_dtenv () in
                    let saved_fenv' = LogicOld.get_fenv () in
                    let restore' () =
                      LogicOld.set_fenv saved_fenv';
                      LogicOld.set_dtenv saved_dtenv';
                      (* the pool again, in the other direction: the nested
                         solve declared the substituted datatypes under the
                         original names, so leaving its instances behind would
                         hand the outer run a context in which those names mean
                         the instantiated sorts *)
                      Z3Smt.Z3interface.clear_instance_pool ();
                      LogicOld.leave_env_bracket ()
                    in
                    let t_nested = Common.Clock.now_s () in
                    let answer =
                      match
                        (LogicOld.set_dtenv dtenv_substituted;
                         LogicOld.set_fenv fenv_substituted;
                         Z3Smt.Z3interface.clear_instance_pool ();
                         (* and IN THE FORM THE SOLVER'S CONTRACT ASKS FOR.
                            The instance is built by substituting sorts into
                            the problem, which preserves its shape, and the
                            shape at this point is not clausal -- the solver
                            being handed it reads the clauses directly and
                            fails with "not of CNF" otherwise.  The measurement
                            route hid this by returning the instance to the
                            outer pipeline, which does the conversion itself;
                            a nested call skips that pipeline and so must do
                            it here.  These are the same three steps the
                            enclosing function takes when preprocessing is
                            switched off entirely. *)
                         let instance =
                           let p = substituted_problem () in
                           Common.PhaseTime.with_phase "finite-instance-cnf"
                             (fun () ->
                               PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf
                               @@ PCSP.Problem.normalize p)
                         in
                         (* bounded, when a budget is set, by a deadline the
                            loop reads between phases: a run past it answers
                            [Timeout], which is discarded like every other
                            answer but [Unsat] *)
                         Common.PhaseTime.with_phase "finite-nested"
                         @@ fun () ->
                         match config.finite_forall_sorts_nested_solve_budget with
                         | None -> solve_instance instance
                         | Some ms ->
                             PCSatCommon.SolveDeadline.within
                               ~strict_budget:
                                 config
                                   .finite_forall_sorts_nested_solve_strict_budget
                               ?after_first_round:
                                 (Option.map
                                    config
                                      .finite_forall_sorts_nested_solve_budget_after_first_round
                                    ~f:(fun ms -> Float.of_int ms /. 1000.))
                               ~seconds:(Float.of_int ms /. 1000.)
                               (fun () -> solve_instance instance))
                      with
                      | v ->
                          restore' ();
                          v
                      | exception e ->
                          restore' ();
                          raise e
                    in
                    finite_log (fun () ->
                        sprintf "size %d nested %s %.2f s %s" n
                          (match answer with
                          | Ok (PCSP.Problem.Unsat _, _) -> "unsat"
                          | Ok (PCSP.Problem.Sat _, _) -> "sat"
                          | Ok (PCSP.Problem.Timeout, _) -> "timeout"
                          | Ok _ -> "no-verdict"
                          | Error _ -> "error")
                          (Common.Clock.now_s () -. t_nested)
                          (match answer with
                          | Ok (_, info) ->
                              sprintf "iters %d" info.State.num_cegis_iters
                          | Error _ -> ""));
                    Debug.print
                    @@ lazy
                         (sprintf "size %d, nested solve answered %s" n
                            (match answer with
                            | Ok (PCSP.Problem.Unsat _, _) -> "unsat"
                            | Ok (PCSP.Problem.Sat _, _) -> "sat"
                            | Ok _ -> "no verdict"
                            | Error _ -> "error"));
                    (match answer with
                    | Ok (PCSP.Problem.Unsat _, info) ->
                        (* the certificate: the nested refutation together
                           with what re-deriving the instance takes -- the
                           problem it was substituted into, the substitution
                           and the environments it was substituted from *)
                        Option.iter info.State.unsat_witness ~f:(fun nested ->
                            finite_certificate :=
                              Some
                                {
                                  UnsatWitness.leaf =
                                    (Map.Poly.empty, Logic.BoolTerm.mk_bool false);
                                  size = n;
                                  smap;
                                  source = pcsp;
                                  dtenv = saved_dtenv;
                                  fenv = saved_fenv;
                                  nested;
                                });
                        `Refuted
                    | _ -> `Undecided)))
          in
          (* up to four, not further.  The expansion grows as n to the power of
             the quantifiers over the sort, so each size costs more than the one
             before, and four is the size the input this was measured on needs:
             it is satisfiable at two and three, so a search that stopped at the
             first satisfiable size would conclude nothing, and one that ran far
             past four would spend its budget building formulas nothing can
             read. *)
          (* and stop at the first size the solver cannot decide rather than
             spending the budget on the sizes above it, which are strictly
             larger formulas over strictly larger domains and so strictly
             harder.  On the input this was written for every size below the
             refuting one is decided, so the stop costs nothing there and bounds
             what the pass costs on a problem it cannot do anything with to a
             single query. *)
          let searched =
            List.fold_until (List.range 1 5) ~init:None
              ~f:(fun _ n ->
                match refuted_at n with
                | `Refuted -> Stop (Some n)
                | `Decided -> Continue None
                | `Undecided -> Stop None)
              ~finish:Fn.id
          in
          match !emitted with
          | Some pcsp' ->
              Debug.print
              @@ lazy
                   "the quantified sorts were substituted rather than decided, \
                    so this run answers about that instance and only its \
                    refutation transfers";
              pcsp'
          | None ->
          match searched with
          | None ->
              Debug.print
              @@ lazy
                   "no size up to 4 refutes the quantified sorts, so nothing \
                    is                     concluded from them";
              pcsp
          | Some n ->
              Debug.print
              @@ lazy
                   (sprintf
                      "the system has no solution when a quantified sort has \
                       %d                        element(s), and a solution \
                       would have to work for every                        \
                       type, so it has none"
                      n);
              PCSP.Problem.of_old_formulas ~params:(PCSP.Problem.params_of pcsp)
              @@ Set.Poly.singleton (Map.Poly.empty, Formula.mk_false ())
      in
      Debug.print @@ lazy "**************** end elim pvars ****************";
      let pcsp, param_logs =
        if not config.drop_constant_args then (pcsp, param_logs)
        else
          let () = stage "drop-constant-args" pcsp in
          let pcsp', added = DimReducer.drop_constant_args ~bpvs pcsp in
          if List.is_empty added then (pcsp, param_logs)
          else (
            Debug.print @@ lazy "constant arguments dropped:";
            Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp');
            (* the new unknowns have every argument still to reduce, and
               their definitions in the answer are over their own signature,
               so they enter the argument record as the unknowns of the
               input do *)
            ( PCSP.Problem.normalize pcsp',
              List.fold added ~init:param_logs ~f:(fun logs (q, sort) ->
                  let args = Logic.Sort.args_of sort in
                  Map.Poly.set logs ~key:(Ident.tvar_to_pvar q)
                    ~data:(Array.init (List.length args) ~f:(fun _ -> true), args))
            ))
      in
      let () = stage "share-determined-args" pcsp in
      let pcsp, param_logs =
        if not config.share_determined_pvar_args then (pcsp, param_logs)
        else
          let pcsp', added =
            share_determined_pvar_args
              ~budget_ms:config.share_determined_pvar_args_budget_ms
              ~fallback_cap:config.share_determined_pvar_args_seq_axiom_fallback_ms
              ~syntactic_first:config.share_determined_syntactic_first
              ~memo_questions:config.share_determined_memo_questions
              ~slice_questions:config.share_determined_slice_questions
              ~bpvs ~timeout:(Some 2000) pcsp
          in
          if List.is_empty added then (pcsp, param_logs)
          else (
            Debug.print @@ lazy "determined arguments shared:";
            Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp');
            ( PCSP.Problem.normalize pcsp',
              List.fold added ~init:param_logs ~f:(fun logs (q, sort) ->
                  let args = Logic.Sort.args_of sort in
                  Map.Poly.set logs ~key:(Ident.tvar_to_pvar q)
                    ~data:(Array.init (List.length args) ~f:(fun _ -> true), args))
            ))
      in
      Debug.print @@ lazy "************* start elim pvar args *************";
      let () = stage "reduce-args" pcsp in
      let pcsp =
        if config.reduce_pvar_args then
          PCSP.Problem.remove_unused_params
          @@ DimReducer.elim_pcsp_args ~bpvs param_logs pcsp
        else pcsp
      in
      let pcsp =
        if config.drop_fn_copy_args then
          let () = stage "drop-fn-copy-args" pcsp in
          PCSP.Problem.remove_unused_params
          @@ DimReducer.drop_fn_copy_args ~bpvs param_logs pcsp
        else pcsp
      in
      Debug.print @@ lazy "************** end elim pvar args **************";
      let oracle =
        match oracle with
        | None -> None
        | Some sol ->
            Debug.print @@ lazy "oracle solution:";
            (* printed with the generic formula printer: the SyGuS printer
               raises on what an SMT-LIB2 oracle may contain (a select, a
               datatype selector), and this line runs only under [verbose], so
               a verbose run of a probe that a plain run completes died here *)
            Debug.print @@ lazy (Ast.CandSolOld.str_of sol);
            Debug.print @@ lazy "";
            let psenv, map = sol in
            Option.some
              ( psenv,
                Set.Poly.map map ~f:(fun (pvar, (senv, phi)) ->
                    let arr, _sargs = Map.Poly.find_exn param_logs pvar in
                    (* a parameter past the unknown's own is kept rather than
                       read past the end of the log, so that an oracle with
                       the wrong number of parameters reaches its consumer
                       with that number, and is reported there, instead of
                       stopping the run here *)
                    ( pvar,
                      ( List.filteri senv ~f:(fun i _bind ->
                            i >= Array.length arr || Array.get arr i),
                        phi ) )) )
      in
      let () = stage "expand-bool" pcsp in
      let pcsp = PCSP.Problem.(remove_unused_params @@ expand_bool pcsp) in
      Debug.print @@ lazy "boolean variables expanded:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let pcsp =
        if config.elim_ite then (
          let pcsp = PCSP.Problem.elim_ite pcsp in
          Debug.print @@ lazy "ite eliminated:";
          Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
          if print_pcsp then (
            Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
            Debug.print @@ lazy "");
          pcsp)
        else pcsp
      in
      let () = stage "elim-triv-nwf" pcsp in
      let pcsp =
        PCSP.Problem.(remove_unused_params @@ elim_triv_nwf_predicate pcsp)
      in
      Debug.print @@ lazy "trivial nwf predicates eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let () = stage "elim-triv-parity" pcsp in
      let pcsp =
        PCSP.Problem.(remove_unused_params @@ elim_triv_parity_predicate pcsp)
      in
      Debug.print @@ lazy "trivial parity predicates eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let () = stage "elim-triv-fn" pcsp in
      let pcsp =
        let pcsp = PCSP.Problem.elim_triv_fn_predicate pcsp in
        Common.PhaseTime.with_phase "unused-params" (fun () ->
            PCSP.Problem.remove_unused_params pcsp)
      in
      let () = stage "restore-witness" pcsp in
      let pcsp =
        if config.restore_witness_universals then
          PCSP.Problem.(
            remove_unused_params @@ restore_witness_universals pcsp)
        else pcsp
      in
      let pcsp =
        if config.elim_fn_feeding_fn then
          PCSP.Problem.(
            remove_unused_params @@ elim_triv_fn_predicate
            @@ elim_fn_feeding_fn_predicate pcsp)
        else pcsp
      in
      Debug.print @@ lazy "trivial fn predicates eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let () = stage "cnf" pcsp in
      let pcsp = PCSP.Problem.to_nnf pcsp in
      Debug.print @@ lazy "NNF transformed:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let pcsp = PCSP.Problem.to_cnf pcsp in
      Debug.print @@ lazy "CNF transformed:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let () = stage "simplify-again" pcsp in
      let pcsp =
        Common.PhaseTime.with_phase "clauses" (fun () ->
            simplify ~timeout:(Some 1000) pcsp)
        |> fun pcsp ->
        share_census "after per-clause simplify" pcsp;
        Common.PhaseTime.with_phase "unused-params" (fun () ->
            PCSP.Problem.remove_unused_params pcsp)
      in
      Debug.print @@ lazy "simplified:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let pcsp =
        if config.cancel_seq_concat_equations then (
          let pcsp =
            PCSP.Problem.map_old pcsp ~f:(fun (uni_senv, phi) ->
                (uni_senv, Evaluator.cancel_seq_concat_equations phi))
          in
          Debug.print @@ lazy "common prefixes and suffixes of sequence equations cancelled:";
          Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
          pcsp)
        else pcsp
      in
      let () = stage "renormalize-again" pcsp in
      let pcsp = PCSP.Problem.normalize pcsp in
      Debug.print @@ lazy "normalized:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let () = stage "normalize-params" pcsp in
      let pcsp =
        if normalize_params then (
          let pcsp =
            PCSP.Problem.(remove_unused_params @@ normalize_uni_senv pcsp)
          in
          Debug.print @@ lazy "universally quantified variables normalized:";
          Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
          if print_pcsp then (
            Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
            Debug.print @@ lazy "");
          pcsp)
        else pcsp
      in
      let () = stage "drop-implied" pcsp in
      let pcsp =
        if config.condense_final_clauses then (
          let pcsp = condense_final_clauses pcsp in
          Debug.print @@ lazy "final clauses condensed:";
          Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
          pcsp)
        else pcsp
      in
      let pcsp =
        if config.drop_implied_body_atoms then (
          let pcsp = drop_implied_body_atoms pcsp in
          Debug.print @@ lazy "premises implied by another premise dropped:";
          Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
          if print_pcsp then (
            Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
            Debug.print @@ lazy "");
          pcsp)
        else pcsp
      in
      Debug.print @@ lazy "*********** preprocessed constraints ***********";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
      Debug.print @@ lazy "************************************************";
      ( oracle,
        let params = PCSP.Problem.params_of pcsp in
        let accounted =
          Set.Poly.union_list
            [
              Map.key_set (PCSP.Problem.senv_of pcsp);
              Map.key_set sol_for_eliminated;
              Map.key_set params.sol_for_eliminated;
              Map.key_set sol_for_resolved;
              Map.key_set params.sol_for_resolved;
              resolved_without_def;
            ]
        in
        PCSP.Problem.update_params pcsp
          {
            params with
            PCSP.Params.args_record = param_logs;
            (* predicates of the original signature that no constraint mentions
               any more and that no elimination accounted for are
               unconstrained: they get a kind-satisfying default so that the
               model is complete *)
            sol_for_eliminated =
              (let merged =
                 Map.Poly.merge sol_for_eliminated params.sol_for_eliminated
                   ~f:(fun ~key:_ -> function
                   | `Left v | `Right v -> Some v
                   | `Both (v, _) -> Some v)
               in
               Map.Poly.fold orig_senv ~init:merged ~f:(fun ~key ~data acc ->
                   if Set.mem accounted key then acc
                   else
                     match
                       PCSP.Problem.default_solution_of_unused
                         (PCSP.Problem.params_of pcsp)
                         key data
                     with
                     | Some t -> Map.Poly.set acc ~key ~data:t
                     | None -> acc));
            PCSP.Params.sol_for_resolved =
              Map.Poly.merge sol_for_resolved params.sol_for_resolved
                ~f:(fun ~key:_ -> function
                | `Left v | `Right v -> Some v
                | `Both (v, _) -> Some v);
            (* the eliminator's reasons, plus [Unused] for the defaults given
               just above: a checker must be able to tell the two logical kinds
               of definition apart *)
            PCSP.Params.elimination_reasons =
              (let m =
                 Map.Poly.merge elimination_reasons params.elimination_reasons
                   ~f:(fun ~key:_ -> function
                   | `Left v | `Right v -> Some v
                   | `Both (v, _) -> Some v)
               in
               Map.Poly.fold orig_senv ~init:m ~f:(fun ~key ~data:_ acc ->
                   if Map.Poly.mem acc key then acc
                   else if Set.mem accounted key then acc
                   else
                     (* after every other step *)
                     Map.Poly.set acc ~key
                       ~data:(PCSP.Params.Unused, Int.max_value)));
          } )

  (* Try the cell abstraction and take only a satisfiable answer from it.

     A solution of the abstracted system concretizes to one of the original --
     each body instance is a consequence of the concretized body, and the head
     is proved at an arbitrary index -- while the original may have a solution
     that no formula over this many cells expresses.  So the abstraction can
     gain an answer and can never justify a refutation, and anything other than
     [Sat] falls through to the problem as given. *)
  let solve_with_cell_abstraction solver pcsp =
    let open Or_error in
    let m = config.cell_abstraction in
    match CellAbstraction.abstract ~m pcsp with
    | None ->
        (match Sys.getenv "COAR_CA" with
         | Some _ -> Stdlib.prerr_endline "[CA] no target unknown"
         | None -> ());
        solver pcsp
    | Some (pcsp', targets) -> (
        (* the abstraction rebuilds the clauses, so they go back through the
           shared normalizations the rest of the pipeline assumes *)
        let pcsp' =
          PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf
          @@ PCSP.Problem.normalize pcsp'
        in
        Debug.print
        @@ lazy
             (sprintf "**** %d-cell abstraction over %d unknown(s)" m
                (Map.Poly.length targets));
        (match Sys.getenv "COAR_CA" with
         | Some _ ->
             Stdlib.prerr_endline
             @@ Printf.sprintf "[CA] abstracted %d unknown(s); clauses %d -> %d"
                  (Map.Poly.length targets)
                  (Set.length (PCSP.Problem.clauses_of pcsp))
                  (Set.length (PCSP.Problem.clauses_of pcsp'))
         | None -> ());
        match solver pcsp' with
        | Ok (PCSP.Problem.Sat sol, info) ->
            Debug.print @@ lazy "**** the abstracted system is satisfiable";
            return
              ( PCSP.Problem.Sat
                  (CellAbstraction.concretize ~m (PCSP.Problem.senv_of pcsp)
                     targets sol),
                info )
        | _ ->
            Debug.print
            @@ lazy
                 "**** the abstracted system gave no solution; solving the \
                  problem as given";
            (match Sys.getenv "COAR_CA" with
             | Some _ -> Stdlib.prerr_endline "[CA] fell back to the original"
             | None -> ());
            solver pcsp)

  (* [word_range_invariants]: solve the problem with the inductive ranges of
     its word arguments as premises of the body atoms, and conjoin them to a
     solution ([PCSatCommon.WordRanges] has the argument).  Every answer of
     the strengthened problem is an answer of the given one, so nothing falls
     back. *)
  let solve_with_word_ranges solver pcsp =
    let open Or_error in
    if not config.word_range_invariants then solver pcsp
    else
      match PCSP.Problem.clauses_of_opt pcsp with
      | None -> solver pcsp
      | Some clauses -> (
          let exi_senv = PCSP.Problem.senv_of pcsp in
          let old = Set.to_list @@ ClauseSet.to_old_clause_set exi_senv clauses in
          let ws =
            PCSatCommon.WordRanges.widths_of
              (List.map old ~f:(fun (_, _, _, phi) -> phi))
          in
          let is_ord p =
            match
              Map.Poly.find (PCSP.Problem.kind_map_of pcsp)
                (Ident.pvar_to_tvar p)
            with
            | Some k -> Kind.is_ord k
            | None -> false
          in
          let cands = PCSatCommon.WordRanges.candidates ~is_ord ws old in
          let id = PCSP.Problem.id_of pcsp in
          let fenv = LogicOld.get_fenv () in
          let ms = config.word_range_invariants_timeout_ms in
          let valid phi =
            (not (Z3Smt.Z3interface.may_not_return phi))
            &&
            match
              PCSatCommon.ForkedQuery.valid_within ~ms:(3 * ms) (fun () ->
                  Z3Smt.Z3interface.check_valid ~timeout:(Some ms) ~id fenv phi)
            with
            | `Valid -> true
            | _ -> false
          in
          let kept =
            if List.is_empty cands then []
            else
              Common.PhaseTime.with_phase "word-ranges" @@ fun () ->
              PCSatCommon.WordRanges.infer ~valid ~cands old
          in
          Debug.print
          @@ lazy
               (sprintf "[word-ranges] widths %s; %d of %d range(s) inductive: %s"
                  (String.concat_map_list ~sep:"," ws ~f:Int.to_string)
                  (List.length kept) (List.length cands)
                  (String.concat_map_list ~sep:", " kept ~f:(fun (p, i, n) ->
                       sprintf "%s#%d<2^%d" (Ident.name_of_pvar p) i n)));
          if List.is_empty kept then solver pcsp
          else
            let pcsp' =
              PCSP.Problem.of_clauses ~params:(PCSP.Problem.params_of pcsp)
              @@ ClauseSet.of_old_clause_set @@ Set.Poly.of_list
              @@ List.map old ~f:(PCSatCommon.WordRanges.strengthen_clause kept)
            in
            solver pcsp' >>| function
            | PCSP.Problem.Sat sol, info ->
                ( PCSP.Problem.Sat
                    (PCSatCommon.WordRanges.strengthen_solution kept exi_senv
                       sol),
                  info )
            | res -> res)

  (* A lint, which changes no answer: for each head application of an
     admissible or integrable unknown, ask whether the clause's constraint,
     with every answer argument in its body non-negative, allows the head's
     answer argument to be negative -- a demand at a value the source
     semantics does not have, which is almost always a mistake in a
     hand-written input.  The relativisation that follows removes such a
     demand whatever this says; the lint only reports it.

     It is locally incomplete: an answer value that reaches the head through
     an ordinary unknown is unconstrained here, since nothing marks that
     unknown's position as an answer position, so a head fed that way is
     reported although the program keeps it non-negative.  That is why this
     warns rather than refuses.  A query Z3 does not decide within a second,
     or whose shape may keep it from returning at all, reports nothing.  It
     runs only when this module's diagnostics are on, since a report is all
     it produces.  It also reports each variable used both at an answer
     position and at a non-answer position of a kinded unknown, whose other
     use the relativisation restricts as well. *)
  let lint_negative_prop_demands pcsp =
    let prop_sorts = PCSP.Problem.prop_sorts_of pcsp in
    if Map.Poly.is_empty prop_sorts || not (Atomic.get Debug.enable) then ()
    else
      try
        let exi_senv = PCSP.Problem.senv_of pcsp in
        let id = PCSP.Problem.id_of pcsp in
        let fenv = LogicOld.get_fenv () in
        let clauses =
          match PCSP.Problem.clauses_of_opt pcsp with
          | Some cls -> cls
          | None ->
              ClauseSet.of_formulas exi_senv
                (PCSP.Problem.formulas_of pcsp)
        in
        (let vs = PCSP.Problem.prop_position_violations pcsp in
         if not (Set.is_empty vs) then
           Debug.print
           @@ lazy
                (sprintf
                   "[warning] %s occur both at an answer position and at a \
                    non-answer position of an admissible or integrable \
                    unknown; restricting the answer position to non-negative \
                    values restricts the other use too"
                   (String.concat_map_set ~sep:", " vs ~f:Ident.name_of_tvar)));
        let open Logic in
        let comps = PCSP.Problem.prop_components_of_app prop_sorts in
        Set.iter clauses ~f:(fun ((uni_senv, ps, ns, phi) as cl) ->
            let body_nonneg =
              List.concat_map (Set.to_list ns) ~f:comps
              |> List.map ~f:(fun w ->
                  ExtTerm.mk_apps (ExtTerm.mk_rleq ()) [ ExtTerm.rzero (); w ])
            in
            Set.iter ps ~f:(fun head ->
                List.iter (comps head) ~f:(fun t ->
                    let query =
                      ExtTerm.to_old_fml exi_senv uni_senv
                      @@ BoolTerm.and_of
                           ((BoolTerm.neg_of phi :: body_nonneg)
                           @ [
                               ExtTerm.mk_apps (ExtTerm.mk_rlt ())
                                 [ t; ExtTerm.rzero () ];
                             ])
                    in
                    if not (Z3Smt.Z3interface.may_not_return query) then
                      match
                        Z3Smt.Z3interface.check_sat ~timeout:(Some 1000) ~id
                          fenv [ query ]
                      with
                      | `Sat _ ->
                          Debug.print
                          @@ lazy
                               (sprintf
                                  "[warning] a clause may demand a negative \
                                   value at an answer position (%s), which \
                                   has no instance in the non-negative \
                                   semantics and is dropped: %s"
                                  (ExtTerm.str_of t)
                                  (Clause.str_of exi_senv cl))
                      | _ -> ())))
      with exn_ when not (Common.Timer.is_async exn_) ->
        Debug.print
        @@ lazy
             (sprintf "[warning] the answer-position lint could not run: %s"
                (Exn.to_string exn_))

  let solve ?(witness = WitnessConfig.default) ?(bpvs = Set.Poly.empty)
      ?(oracle = None) ?nested_solver ?(extend = true) ?post_elim
      (solver :
        ?oracle:PCSP.Problem.oracle -> PCSP.Problem.t -> State.output Or_error.t)
      pcsp =
    Debug.set_id @@ PCSP.Problem.id_of pcsp;
    PvarEliminator.id := PCSP.Problem.id_of pcsp;
    (* before the split below: with preprocessing disabled [preprocess] never
       runs, and the relativisation is a reading of the problem, not an
       optimisation *)
    LogicOld.unify_negated_linear := config.unify_negated_linear;
    ClauseOld.condense_up_to_linear := config.condense_up_to_linear;
    lint_negative_prop_demands pcsp;
    let pcsp =
      if config.relativise_prop_positions then
        PCSP.Problem.relativise_prop_positions pcsp
      else pcsp
    in
    if config.enable then (
      incr solve_depth;
      (fun f -> Exn.protect ~f ~finally:(fun () -> decr solve_depth))
      @@ fun () ->
      let finite_certificate = ref None in
      let finite_race = ref [] in
      (* the races are finished, the newest first, however this returns: a
         copy that refutes after the process has its answer is killed, and a
         copy that was handed the run makes [finish] never return *)
      (fun f ->
        Exn.protect ~f ~finally:(fun () ->
            List.iter !finite_race ~f:PCSatCommon.ParallelRace.finish;
            finite_race := []))
      @@ fun () ->
      let oracle, pcsp =
        let bpvs =
          Set.union bpvs @@ ClauseSet.pvs_of
          @@ PCSP.Problem.stable_clauses_of pcsp
        in
        preprocess ~witness ~bpvs ~oracle ~normalize_params:true
          ~finite_certificate ~finite_race ?post_elim ~solver:
            (Some
               (match nested_solver with
               | Some nested
                 when config.finite_forall_sorts_nested_solve_fresh_context ->
                   nested
               | _ -> solver ~oracle:None))
          pcsp
      in
      (* [race_drop_duplicate_copies]: a raced copy whose preprocessed problem
         is this one is dropped (see [ParallelRace.Duplicate]); only the
         outermost solve of a process compares *)
      if !solve_depth = 1 then
        Common.PhaseTime.with_phase "race-digest" (fun () ->
            PCSatCommon.ParallelRace.Duplicate.checkpoint
              ~log:(fun msg -> Debug.print @@ lazy ("[race] " ^ msg))
              (lazy (RaceDigest.of_problem pcsp)));
      (* parameters are recovered inside [solve_and_extend], before closure.
         The cell abstraction goes *inside* that, so the extension still sees
         the problem whose elimination records it has to replay. *)
      let open Or_error in
      solve_and_extend ~extend
        (solve_with_word_ranges (fun p ->
             if config.cell_abstraction > 0 then
               solve_with_cell_abstraction (solver ~oracle) p
             else solver ~oracle p))
        pcsp
      >>| fun (sol, info) ->
      (* A [false] constraint the finite instantiation produced is only a
         leaf; the refutation behind it is the certificate it left, which the
         witness then carries in place of the bare leaf.  Once the pass has
         refuted, the problem handed on is the single constraint [false], so
         a [false] leaf reported for it is that one. *)
      match (!finite_certificate, info.State.unsat_witness) with
      | ( Some cert,
          Some
            ({ UnsatWitness.body = UnsatWitness.FalseConstraint (u, t); _ } as w)
        ) ->
          ( sol,
            {
              info with
              State.unsat_witness =
                Some
                  {
                    w with
                    UnsatWitness.body =
                      UnsatWitness.FiniteInstance { cert with leaf = (u, t) };
                  };
            } )
      | _ -> (sol, info))
    else
      let pcsp =
        PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf
        @@ PCSP.Problem.normalize pcsp
      in
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
      if config.cell_abstraction > 0 then
        solve_with_cell_abstraction (solver ~oracle) pcsp
      else solver ~oracle pcsp
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : PreprocessorType)
