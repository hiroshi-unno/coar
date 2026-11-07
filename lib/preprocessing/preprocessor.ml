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
  (** During predicate elimination, when the validity question of a clause
      with no predicate application and no unknown is asked.  Resolution never
      touches such a clause and no elimination rule counts it, so the question
      is the same at each simplification of a round.  Both postponements are
      exact: an unasked question keeps its clause. *)
  type defer_pure =
    | Ask_in_round  (** asked at every simplification, as for any clause *)
    | Defer_to_round_end
        (** not asked while a round resolves; the round's last
            simplification asks the elimination's own question of each
            postponed clause whether or not an unknown remains, so each pure
            clause is asked once per round instead of at every simplification
            (an undecided one was asked again at the re-ask budget at each
            later simplification of its round) *)
    | Defer_to_verdict
        (** not asked while a round resolves; at the round's last
            simplification it is asked as before when an unknown remains, and
            otherwise only through the words of its matched-instance forms (as
            [elimination.questions.words.first] asks them), only a proof read, the clause
            otherwise kept for the zero-unknown verdict.  Why: on a bit-set
            input three such questions stayed undecided at about nine seconds
            each (native budget, sequence-axiom fallback) and were asked again
            at later simplifications, while the verdict proved the same
            clauses, one by its pieces in under a second *)
  [@@deriving yojson]

  (** How much physical sharing the preprocessing passes that rebuild every
      formula of a problem keep.  The output is the one the passes give
      without sharing, value for value and with the same fresh-name draws;
      only its sharing differs. *)
  type formula_sharing =
    | No_sharing  (** each formula converted and rebuilt on its own *)
    | Term_conversions
        (** the round trips between the two term representations that the
            preprocessing passes make over a whole problem
            ([PCSP.Problem.map_raw_old_exn]) keep physical sharing: each
            direction remembers the image of every formula node by physical
            identity inside one call
            ([Logic.ExtTerm.with_shared_term_conversion]), and the
            trivial-functional-predicate pass puts the whole problem in
            negation and clausal normal form inside one table
            ([with_shared_nnf_cnf]).  The same formulas up to physical sharing
            (and up to the bound names a beta-redex in a formula position draws
            when converted).  Why: a clausal form that multiplies alternatives
            gives thousands of clauses built from the same physical
            subformulas, and each per-formula conversion copied the shared
            parts once per clause, so a set held in megabytes as built held
            gigabytes after the elimination and every later pass walked and
            copied them *)
    | Rebuilt_formulas
        (** as [Term_conversions], and every pass that rebuilds the formulas
            keeps the sharing of its input, each by a table keyed by node
            address that lives for one call: the round trips remember term
            images as well as formula images, remembering an image only when
            computing it drew no fresh name, and the simplifier, the
            normaliser and the unused-parameter pass share theirs.  Why: on an
            input whose elimination multiplies a clause into thousands, the
            clauses' large pure parts are one physical value when built, and
            each pass that rebuilt the formulas one by one made a copy per
            clause, so every later pass compared and walked the copies -- 2.3
            million nodes as built, 50 million after one conversion *)
  [@@deriving yojson]

  (** How the same-name syntactic subsumption of predicate elimination is
      computed.  Every implementation keeps and drops the same clauses, and
      builds the result by the same insertions; only the cost differs. *)
  type subsume_impl =
    | Plain  (** every pair of literal sets compared structurally *)
    | Hashed
        (** each literal's hash, each clause's set of hashes, inclusion of the
            hash sets tested before the literal sets.  Why: on a Thrust closure
            input the polymorphic comparison of large formulas in subsumption
            took most of a 49-54 s bound assignment step, 31-33 s with the
            hashes *)
    | Interned
        (** every literal interned once per call to an integer by a table whose
            equality is the literal sets' own polymorphic [compare], each
            clause's literal set an ascending id array, and each kept clause
            indexed under its literal occurring in the fewest clauses of the
            call.  Why: on a Thrust closure input whose clauses share a large
            pure disjunct, the hashed version still tested every pair of
            clauses keyed by that disjunct, and subsumption was the largest
            single cost of a preprocessing that spent no time in the solver *)
    | Persistent
        (** [Interned] with its interning tables kept from one call to the next
            (in a domain, from the start of an elimination), pruned after each
            call to the literals of the clauses kept, so that a literal met
            before is found by its physical identity and not hashed deeply
            again ([PvarEliminator.ClauseSubsume.reduce_persistent]).  Why: the
            clauses a resolution step leaves alone are the same values in the
            next step, and on a Thrust input of 600 clauses whose resolvents
            have over a hundred disjuncts, hashing every literal of every clause
            at every step was the largest part of a subsumption that took a
            fifth of the predicate elimination *)
  [@@deriving yojson]

  (** During predicate elimination, whether every clause whose literals
      (positive atoms, negative atoms, disjuncts of the pure part) are a
      superset of another clause's, compared syntactically under the same
      variable names, is dropped: after the conjunctive normal form, after the
      one-sided and bound assignments, and on each resolution step's result.
      Exact: the subsumer implies the clause it subsumes, so the clause set
      keeps its models, and a definition recovered for an eliminated predicate
      from the reduced set satisfies the original one.  What it buys: a body
      conjunct [discr = k => P payload] doubles the normal form, and once [P] is
      assigned [true] the copies differ only by pure literals, each a superset
      of one of them; on the Thrust fuse pair it takes resolution's input from
      113 to 22 clauses and its largest step from 768 resolvents to 6. *)
  type elim_subsume =
    | No_subsume
    | Subsume of {
        impl : subsume_impl; [@default Persistent]
        resolution_index : bool; [@default true]
            (** the resolution rounds keep, across the steps of one chain, the
                clauses applying each predicate, the occurrence counts and each
                clause's interned literals ([PvarEliminator.ResolutionIndex]),
                so a step reads only the clauses applying the predicate it
                resolves and the new resolvents: the same counts, the same
                candidates and the same subsumption decisions, hence the same
                clause set built by the same insertions.  Why: on a Thrust
                closure input whose clausal form has 2,400 clauses of 9.4
                million nodes, each step resolving an auxiliary predicate in a
                few clauses spent 0.14-0.97 s walking the whole set (counting
                occurrences and subsuming); with the index that round's
                whole-set work fell from 64 s to 8 s.  Off: every step counts
                and subsumes the whole set *)
      }
  [@@deriving yojson]

  (** When elimination by resolution stops because every remaining unknown
      would grow the clause set past [elimination.resolution_threshold],
      whether it tries to resolve ALL of them away anyway, keeping the result
      only if no unknown is left and the clause set never exceeded a bound;
      otherwise the clause set and the recorded definitions are put back as
      they were.  Resolution
      is an equivalence of satisfiability whatever the threshold, so this is
      sound for both answers; what it changes is the question the rest of the
      run is asked -- a validity check of finitely many clauses, decided by the
      zero-unknown verdict, in place of a search for solutions in a hypothesis
      space that may not contain one (a solution needing an existential, for
      instance).  Over 325 Thrust, quantified-invariant and CHC inputs at 120 s
      the attempt with a bound of 100 answered 284.4 expected against 282.6
      without, with no verdict disagreement; the Thrust fuse queries went from
      0 of 5 to 5 of 5, and the files it answered less often each moved by one
      run of five. *)
  type resolution_complete =
    | No_complete_elimination  (** the threshold's stop is final *)
    | Complete_elimination of {
        max_clauses : int; [@default 100]
            (** the bound on the clause set during the attempt; a bound of 0
                or less tries nothing *)
        prebound : bool; [@default false]
            (** before resolving an unknown away, predict the clause set's size
                as the clauses that do not mention it plus the number of
                resolvents the step builds (with one occurrence per clause,
                its positive times its negative occurrences, the threshold's
                own accounting; a body repeating it [k] times against [p]
                definitions builds [p ^ k]) and abandon the attempt, building
                and asking nothing of that step, when the prediction exceeds
                [max_clauses].  The prediction is exact when every resolvent
                becomes one clause that simplification keeps and no two
                coincide; where simplification drops resolvents (proved valid)
                it is too large and this can abandon an attempt the full build
                would have kept, and where a resolvent splits into several
                clauses it is too small and the full build's own test still
                applies.  Either way the answer cannot change, only whether the
                rest of the run is asked about the eliminated clause set.  What
                it buys: a step resolving 512 or 768 resolvents, each with a
                validity question of seconds, is not built when it is predicted
                to exceed the bound.  Off: the test is only the one after each
                step is built *)
        early_exit : bool; [@default true]
            (** stop building a step as soon as the clause set built so far
                exceeds [max_clauses], instead of finishing the step and
                testing then.  Exact: the resolvents are simplified in the same
                order, the set only grows while it is built, so the attempt is
                abandoned with it on exactly when it is abandoned with it off,
                and kept with the same clause set otherwise; what it saves is
                the validity questions of the resolvents after the bound is
                crossed *)
        budget_ms : int option; [@default None]
            (** a wall-clock budget, in milliseconds, for one attempt, read
                before each step and before each resolvent's simplification;
                when it is spent the attempt is abandoned as if it had exceeded
                its bound (the clause set and the recorded definitions put
                back).  A load-dependent cut, so unlike the two switches above
                it can change which clause set the rest of the run is asked
                about between two runs; never the soundness of the answer.
                [None] sets no budget *)
        invalid_first_ms : int option; [@default None]
            (** with [early_exit], [Some ms] first asks each resolvent of a
                step its validity question under [ms] ms, in the order of the
                build, and abandons the step as soon as the resolvents shown
                invalid there (with those kept without a question) prove that
                the clause set built will exceed [max_clauses]
                ([PvarEliminator.InvalidFirst]); otherwise the step is built
                as without it.  Exact: a resolvent with an invalid question is
                never dropped by simplification, whatever the full budget
                answers, and keeps its environment and atoms, so the distinct
                environment-and-atoms triples among those resolvents that no
                clause outside the step has, added to the clauses outside the
                step, are a lower bound on the size the early exit tests (before
                subsumption); a step abandoned by it is one the early exit
                abandons, so the attempt's outcome and kept clause set are
                unchanged, and only the cost moves.  What it buys: an invalid
                question is answered in hundredths of a second where a valid
                or undecided one takes the full budget, so on a Rust-derived
                input whose complete attempt asked 76 questions of 5-11 s before
                its early exit fired the step can end after the short pass.
                Off (the default): every step built as before *)
        skip_recursive : bool; [@default false]
            (** do not try when some unknown occurs on both sides of one clause
                (as an invariant does in its step clause).  Resolving another
                unknown away leaves every resolvent of such a clause with that
                unknown on both sides, and the eliminator never resolves away an
                unknown while it does, so the attempt can keep its result only
                if simplification or subsumption drops every descendant of each
                such clause.  Not exact for that reason: it gives up those
                attempts.  What it buys: on a k-safety product with one arbiter
                per schedule of three copies, each attempt resolved the seven
                arbiters out of a disjunctive scheduling clause (2, 4, ... 49
                resolvents, each carrying a copy of the step relation) and was
                then abandoned with the invariant left, twice per run.  Off: the
                attempt is made whatever the clauses *)
      }
  [@@deriving yojson]

  (** Formulas set aside from the clausal form of a round of predicate
      elimination ([max_clauses]), and how they are put in clausal form after
      the last round ([definitional], read only with [max_clauses]).  Read by
      this preprocessor's eliminator only: two solvers in one process (MuVal's
      primal and dual) each follow their own configuration's value, so the
      split can be given to one side by giving that side's solver a
      configuration that asks for it. *)
  (** Which variables a fresh unknown of the definitional clausal form takes
      ([PvarEliminator.definitional_split]). *)
  type definitional_args =
    | All_free
        (** every free term variable of the named disjunct and every Boolean
            universal of its clause *)
    | Shared
        (** only those the disjunct shares with the rest of its formula: a
            variable free in the disjunct alone is quantified inside the
            definition, which keeps the satisfiability both ways
            ([forall y. (A \/ c)] is [A \/ forall y. c] when [y] is not free
            in [A]).  Why: on the non-termination side of an integer
            transition system whose path steps are inlined one into the next,
            every deeper step's choice variables are free in each step's
            disjunct, and [All_free] gave fresh unknowns of up to 464
            arguments *)
  [@@deriving yojson]

  (** Which formulas are set aside and which disjuncts the definitional
      clausal form names. *)
  type set_aside_naming =
    | Every_multiplied
        (** a formula is set aside whenever its predicted clausal form
            exceeds the bound, and the split names every disjunct of more
            than one clause in a disjunction over the bound *)
    | Gaining_only
        (** a formula is set aside only when its clausal form exceeds the
            bound through a product that a fresh unknown shortens, and the
            split names a disjunct only where naming it shortens the clausal
            form: in a disjunction whose other disjuncts give [p] clauses, a
            disjunct of [c] clauses is named only when [(p - 1) * (c - 1) > 1],
            the largest first and only while the product exceeds the bound;
            where no naming shortens it, the largest disjunct is distributed
            over the others as the plain clausal form does.  The same rule on
            every side of a problem.  Why: a fresh unknown is a second
            unknown for the synthesiser to find; one named beside a single
            clause ([U(xs) => /\_i (guard_i => successor_i)], the proving side
            of a transition system) stood between the invariant and every
            obligation it had, saved no clause, and turned a two-round
            refutation into one that did not converge *)
  [@@deriving yojson]

  type elimination_set_aside = {
    max_clauses : int option; [@default None]
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
    definitional_args : definitional_args; [@default All_free]
        (** with [definitional]: the fresh unknowns' arguments *)
    naming : set_aside_naming; [@default Every_multiplied]
        (** with [max_clauses]: which formulas are set aside and, with
            [definitional], which disjuncts are named *)
    trigger_clauses : int option; [@default None]
        (** with [max_clauses = Some n]: [Some t] sets a formula aside only
            when its predicted clausal form exceeds [max t n] (and, under
            [Gaining_only], a fresh unknown shortens it); a formula at or
            below that count is put in clausal form with the round exactly as
            without the switch, while one set aside is still named down to
            [n] by [definitional].  [None]: the trigger is [n] itself.  Sound
            for any [t]: it only chooses which formulas the set-aside and the
            definitional split (each sound for any formula) are applied to.
            Why: the split pays where the distribution is a product the run
            cannot afford -- the non-termination side of a path-composed
            transition system, where one formula of a few thousand nodes
            predicts 10^6 to 3 x 10^8 clauses and its clausal form fills the
            run or the memory cap -- and costs where it is not, since a named
            disjunct is one more unknown to synthesise and a set-aside formula
            keeps its unknowns from elimination: with the trigger at the bound
            of 100 the split lost one input's answer (4 of 4 runs to 1 of 4)
            and doubled the summed time on a corpus of muCLP inputs (264 to
            578 s), whose formulas are small.  A trigger
            far above the bound leaves every formula under it as it was and
            splits only the multiplied ones, finely *)
    definitional : bool; [@default false]
        (** with [max_clauses = Some n]: a formula set aside
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
  }
  [@@deriving yojson]

  (** Exact speed-ups of predicate elimination: each computes the same clause
      set by a cheaper route. *)
  type elimination_speed = {
    cnf_shared_fvs : bool; [@default true]
        (** the clausal form of predicate elimination reduces each clause's
            sort map with the free variables of its atoms and of its pure
            part's disjuncts remembered by physical identity across the call
            ([ClauseOld.reduce_sort_map_shared]): the same maps as without it.
            Why: the normal form gives thousands of clauses sharing large pure
            disjuncts, and their free variables were recomputed per clause,
            the largest part of a 24-31 s conversion on a Thrust closure
            input.  On by default (an exact speedup). *)
    resolution_atom_pvs_memo : bool; [@default true]
        (** the resolution rounds of predicate elimination read each atom's
            predicate variables ([Atom.pvs_of]) through a table keyed by
            physical identity, kept across the rounds of one elimination:
            the same sets, so the same choices.  Why: the clauses a round
            leaves alone are the same values in the next, and walking every
            atom's argument terms once per round was most of the rounds'
            candidate choice on a Thrust closure input.  On by default (an
            exact speedup). *)
    reuse_unassigned_cnf : bool; [@default true]
        (** when the bounds step of predicate elimination assigns constants
            ([elimination.assign_before_cnf]) and builds the clausal form again from
            the substituted formulas, a formula the substitution leaves
            structurally as it was gets the clauses its first clausal form
            gave (kept per formula, after the sort maps and the tautology
            test) instead of a second clausal form: the same clause set.
            Why: on a Thrust input with 465 formulas of up to ~120-argument
            unknowns the second clausal form cost as much as the first
            (21-28 s), and the substitution touched few of the formulas.  On
            by default (an exact speedup). *)
    cnf_clause_tree : bool; [@default true]
        (** the clausal form of predicate elimination reads an input formula
            that is already one clause (a tree of disjunctions over
            unknown-free subtrees and signed applications of unknowns) in one
            pass ([Formula.cnf_of_clause_tree]): the same clauses as without
            it.  Why: a round after the first reads back the clauses the round
            before produced, and on a Thrust closure input with 2,376 of them
            the normal form walked every large pure disjunct once per
            disjunction above it. *)
    triv_fn_linear : bool; [@default true]
        (** the pass that drops trivial functional body atoms reads the free
            variables of each of a clause's k functional body atoms once,
            rather than those of the k - 1 others for each of them (k^2
            walks), and the rest of the clause's only when some result is a
            variable; the same answers, so the same output.  Why: on a
            Thrust input whose clauses hold 21 to 33 such atoms over large
            arguments, the k^2 walks were most of a 150 s pass *)
  }
  [@@deriving yojson]

  type elimination_memo =
    | No_memo  (** every question asked as it comes *)
    | Memo of {
        alpha : bool; [@default true]
            (** with [elimination.questions.memo], key the record up to a renaming of the
                question's variables, free and bound, as well as up to the order
                of its disjuncts and of each quantifier block: validity is a
                property of the universal closure, which such a renaming does not
                change, so two clauses that differ only in their variables' names
                share one answer.  Off keeps the key that is only up to the
                orders. *)
        reasks : int; [@default 4]
            (** with [elimination.questions.memo], how many more times a query that ran
                out of its budget is asked before the record answers it as
                undecided.  A decided answer, and a shape the solver is not asked
                about, are recorded at once; a timeout is not, since one query's
                text can run out of the full budget twice and then be proved in a
                twentieth of a second *)
        reask_timeout_ms : int; [@default 500]
            (** the budget, in milliseconds, of each such repeated ask *)
        reask_max_disjuncts : int; [@default 64]
            (** with [elimination.questions.memo], a timed-out query is asked again only
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
      }  (** the record of earlier answers, with its re-asks *)
  [@@deriving yojson]

  (** The sequence-axiom fallback of predicate elimination's validity
      questions: its budget, its cap per question, and when it is asked. *)
  type elimination_seq_axiom_fallback = {
    cap_ms : int option; [@default None]
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
    budget_ms : int option; [@default Some 3000]
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
    once : bool; [@default false]
        (** with [elimination.questions.memo], a timed-out question that the record
            asks again does not ask the sequence-axiom fallback again unless
            the fallback's budget on the repeated ask would be larger than on
            the first, which it is not under the default budgets (the fallback
            runs with the smaller of its own budget and the question's, 500 ms
            both times).  The repeated native ask is unchanged.  Same
            soundness argument as above: not asking keeps the clause. *)
    after_refusal_only : bool; [@default false]
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
    charge_build : bool; [@default false]
        (** during predicate elimination, count the time the sequence-axiom
            fallback spends building its question (the translation, the
            negation normal form, the conversion of the goal) against the
            fallback's budget, and do not ask the solver once that budget is
            spent; otherwise the budget bounds the solver call alone.  Why: on a
            large Rust-derived input the build took about 2 s per question
            against a 500 ms budget, 37 of the 42 s the fallback cost there.
            Same soundness argument as above: a question not asked keeps the
            clause. *)
    rlimit : int option; [@default Some 650000]
        (** a Z3 resource limit per question of the sequence-axiom fallback
            asked by the same checks (see [elimination.questions.seq_axiom_fallback.cap_ms]),
            beside the fallback's wall-clock budget, which stays as the kill
            for a check Z3 does not interrupt.  Separate from
            [elimination.questions.rlimit] because the fallback asks the axiomatised
            form in a context of its own, so its count is another quantity.
            An exhausted limit leaves the question as the native check left
            it.  [None] sets none *)
  }
  [@@deriving yojson]

  (** Which of predicate elimination's validity questions are asked in a
      forked copy killed at a budget. *)
  type elimination_fork = {
    refused_ms : int option; [@default None]
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
    quantified_margin_ms : int option; [@default None]
        (** during predicate elimination, every validity question with a
            quantifier that would be asked in this process (the native ask of
            a question the shape test admits, and the bounded decidability
            questions of the functional-predicate rules) is asked in a forked
            copy with no Z3 timer, killed after the question's budget plus
            this many milliseconds. A proof or refutation is read back (the
            latter without its model); a kill or a crash leaves the question
            undecided and its clause kept.  [None] asks in process, except
            a bounded question of a shape the solver boundary refuses (a
            quantifier binding a sequence), which is not asked and reads as
            undecided; with [Some m] such a question is asked in the copy.  Sound: the
            copy's proof is the solver's proof of the same question.  Why:
            Z3 5.1.0's sequence theory has a loop that reads neither its
            timeout nor its resource limit, so only a killed process bounds
            such a question; on a Rust-derived input one elimination
            question stayed open in process for 221 s at 5.5 GB. *)
    seq_unreturning : bool; [@default true]
        (** during predicate elimination, a validity question with a
            quantifier that reads a sequence (and is not already asked in a
            copy under [quantified_margin_ms]) has its native check asked in
            a forked copy with the question's own Z3 budget, killed a second
            after it; a proof comes back as it is, a refutation is asked
            again in process for its model, and a kill reads as the budget's
            timeout, after which the sequence-axiom fallback runs in process
            as before.  The same answers as asking in process whenever that
            call honours its budget.  A WORKAROUND for Z3 5.1.0 ignoring its
            timeout in a context that has been in a scope (the newest z3 in
            opam-repository is 5.1.0): one elimination question of a
            Rust-derived input, left undecided at its 5 s budget in fourteen
            runs of fifteen, grew past the 6 GB memory cap in the fifteenth.
            Remove it, with [pins.seq_lengths.fork_unreturning] of the
            no-unknown configuration, when the reproducer row for
            [benchmarks/SMT/simple/z3_seq_pin_scoped_timeout_unsat.smt2] in
            [script/rerun_external_reproducers.sh] reports GONE for the Z3
            that opam installs.  [false]: asked in process *)
  }
  [@@deriving yojson]

  (** cvc5's questions in predicate elimination: the retry of a question Z3
      left undecided, and cvc5's resource count. *)
  type elimination_cvc5 = {
    retry_ms : int option; [@default None]
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
    rlimit : int option; [@default None]
        (** cvc5's resource limit ([--rlimit-per], cvc5's own unit) for the
            elimination's cvc5 retry ([elimination.questions.cvc5.retry_ms]); with
            [elimination.questions.kill_factor] set too, the retry's wall clock is
            that multiple of its budget.  [None] sets none *)
  }
  [@@deriving yojson]

  (** The words route of predicate elimination's validity questions (the
      matched-instance forms of a question asked as words first). *)
  type elimination_words = {
    first : bool; [@default true]
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
    keep_proved : bool; [@default false]
        (** with [elimination.questions.words.first], the words route goes through every
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
    full_major_every : int option; [@default None]
        (** while predicate elimination asks a question through its words
            ([elimination.questions.words.first], [elimination.questions.defer_pure]'s
            [Defer_to_verdict]), the
            forced major collection before a new Z3 context is made before
            every n-th context only instead of before each; every words
            question is a context of its own, and on a bit-set input the
            collections were a fifth of the words questions' time (0.24 s
            each over the heap the elimination has built), most of them before
            questions that proved nothing.  The questions are the same; at
            most n dropped contexts wait for the collector at once.  [None]
            keeps the process-wide setting *)
    skip_spent_searches : bool; [@default true]
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
  }
  [@@deriving yojson]

  (** The exact rewrites a validity question of predicate elimination is
      given before it is asked ([Ast.QuestionRewrites]). *)
  type elimination_rewrites = {
    onepoint : bool; [@default true]
        (** each validity question the predicate eliminator asks that still
            has a binder is asked after the one-point rule, the binder splits
            and the singleton-range rule
            ([Evaluator.elim_onepoint_singleton_and_split_binders]), as the
            validator's [onepoint_validation_questions] does: a bound variable
            a top-level equation of its binder's body fixes is replaced by the
            term it equals.  Exact: the question asked is equivalent to the
            original in every model, so it is valid exactly when the original
            is.  Why: a [let] of the input reaches a resolvent as
            [exists x. 0 = x - t /\ phi], and Z3's default strategy left such
            questions over [int_to_bv] and sequence reads undecided at their
            budget while, with the binder eliminated, they were [unsat] in
            under a second.  Process-wide once on.  Being exact, it still
            changes which questions decide within their budget and so which
            clauses elimination drops on every input; it is on by default
            because on the inputs it acts on it lost no answer and gave no
            other verdict.  Off: asked as built *)
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
    guarded_length_only_sequences : bool; [@default false]
        (** during predicate elimination, ask each validity question with every
            integer-sequence variable it observes only through its length and
            through element guards (a premise "every element is in [lo, hi)")
            replaced by a non-negative integer, when the constant sequence of
            one element makes every guard hold whatever the theory gives a
            read outside the sequence
            ([Evaluator.eliminate_guarded_length_only_sequences]; each such
            check a small quantifier-free question under a resource limit).
            Exact: the rewritten question is valid iff the question is.  What
            it buys: on Rust-derived inputs whose integers are range-checked,
            a resolvent's question over [seq.len] and the element ranges of a
            sequence goes to the sequence solver, which is slow on lengths and
            cannot build a long one; the integer question is linear.  Off by
            default: a question decided that was not changes the clause set
            every later phase sees, so it is measured as an arm first *)
    split_seq_prefix_over_concat : bool; [@default false]
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
    split_int_binders_at_ite : bool; [@default true]
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
    implied_factor_equalities : bool; [@default false]
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
            seed.  Off by default: it asks a question per pair of factors
            before every elimination question with a product, and the input
            it was turned on for (a bit-set loop whose obligation it decided)
            now answers in the same time without it, so no input is known to
            need it. *)
  }
  [@@deriving yojson]

  (** The budgets of asking a validity question of predicate elimination
      piece by piece first ([pieces_first]). *)
  type elimination_pieces_first = {
    z3_ms : int; [@default 1000]  (** each piece natively under this budget *)
    cvc5_ms : int option; [@default None]
        (** when Z3 leaves a piece undecided, cvc5 under this budget; [None]:
            no cvc5 question *)
  }
  [@@deriving yojson]

  (** Predicate elimination's validity questions (a resolvent or clause
      asked valid so that it can be dropped): budgets, the record of earlier
      answers, fallbacks, forks and rewrites. *)
  type elimination_questions = {
    timeout_ms : int; [@default 5000]
        (** the wall-clock budget, in milliseconds, of each validity query the
            predicate eliminator asks while simplifying a clause
            ([PvarEliminator.check_valid]).  An undecided query keeps every
            disjunct of the clause, so a budget that runs out costs a
            simplification and never a wrong verdict; but the clauses that are
            left are what the rest of the run -- the zero-unknown verdict
            among it -- is asked about, so under load a query decided on an idle
            machine can leave a harder clause set behind *)
    rlimit : int option; [@default None]
        (** a Z3 resource limit ([rlimit], a count of the solver's own steps,
            independent of load) per check of the same validity questions --
            every check one question makes: the native ask and its fresh
            retry, the words route's forms, the factor-equality checks, the
            forked ask of a refused shape (the sequence-axiom fallback keeps
            [elimination.questions.seq_axiom_fallback.rlimit]) -- beside the wall-clock budget,
            which stays unless [elimination.questions.kill_factor] is set; [None] sets
            none *)
    kill_factor : int option; [@default None]
        (** with [elimination.questions.rlimit] set, the wall-clock budget of every
            check of those questions (the fallback's and the forked ask's
            included) becomes this many times the budget it had
            ([elimination.questions.timeout_ms], the re-ask budget, the fallback's
            budget; a re-ask under the first ask's count, [reask_rlimit] unset,
            takes the multiple of [timeout_ms], the budget its count belongs to,
            since a multiple of the short re-ask budget cut such re-asks by the
            wall clock before the count): the count decides and the wall clock only kills a check
            whose counter does not grow, so a question's outcome does not
            depend on the machine's load.  A multiple because Z3's counter
            advances at rates from thousands to hundreds of thousands of units
            a second.  The warm re-ask, a split of a wall-clock budget, is
            then not used. The fallback's base budget is multiplied, but
            [elimination.questions.seq_axiom_fallback.cap_ms] remains an absolute cap; zero
            still disables the fallback. [None] keeps the wall-clock budgets *)
    reask_rlimit : int option; [@default None]
        (** with [elimination.questions.rlimit] set, the resource limit of a
            question the record asks again after it ran out
            ([elimination.questions.memo.reasks]); [None] gives a re-ask the first
            ask's limit *)
    fresh_quantified : bool; [@default false]
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
    memo : elimination_memo;
        [@default Common.Util.config_default elimination_memo_of_yojson {|["Memo", {}]|}]
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
            ([elimination.questions.memo.reasks]): answering it from the record
            kept a clause the next ask would have proved in a twentieth of a
            second, and the zero-unknown verdict then spent its budget on
            that clause.  On by default: over 359 Thrust, quantified-invariant and CHC
            inputs at 120 s it answered 302.4 expected against 301.2 without, with no
            verdict disagreement. *)
    warm_reask_ms : int option; [@default None]
        (** [Some ms]: each validity question of the predicate elimination is
            first asked with a budget of [ms] milliseconds (at most
            [elimination.questions.timeout_ms]) and without the sequence-axiom
            fallback; if that is undecided it is asked again AT ONCE, in the
            same pooled solver, with the rest of [elimination.questions.timeout_ms] and
            the fallback as configured.  A question recorded as undecided is
            then answered from the record and never asked again, so the
            repeated asks of [elimination.questions.memo.reasks] do not happen.
            Why: a quantifier-free question undecided at 5 s in a solver of
            its own, under every seed, was decided in 0.03 s when asked again
            in a new scope of the solver that had tried it inside a scope for
            100 ms or more (and not after a first try of 10 ms, nor after a
            reset); every decided check in two traced eliminations took at
            most 0.32 s.  So the re-ask is a two-phase solve, which this
            makes deliberate rather than a later repeat that lands in a
            solver other questions have used in between.  [None] (the
            default): one ask with the full budget, repeated as above. *)
    defer_pure : defer_pure; [@default Ask_in_round]
        (** during predicate elimination, when the validity question of a
            clause with no predicate application and no unknown is asked (see
            [defer_pure]) *)
    defer_pure_min_disjuncts : int option; [@default Some 256]
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
    seq_axiom_fallback : elimination_seq_axiom_fallback;
        [@default Common.Util.config_default elimination_seq_axiom_fallback_of_yojson "{}"]
    axioms_first_ms : int option; [@default None]
        (** during predicate elimination, a validity question that mentions
            a sequence and is asked natively is first asked with the
            sequences axiomatised under [Some ms] milliseconds (at most the
            question's budget), and only a proof is read from that ask;
            anything else asks the question natively as without this.  The
            same proof the sequence-axiom fallback reads after an undecided
            native ask, asked before it: sound, and it changes which ask
            decides a question, never what a decision says.  Why: on a
            Rust-derived input the native solver ran out of its whole budget
            on questions the axiom form then proved in 0.03-0.3 s.  [None]:
            the native question first, as before *)
    fork : elimination_fork;
        [@default Common.Util.config_default elimination_fork_of_yojson "{}"]
    cvc5 : elimination_cvc5;
        [@default Common.Util.config_default elimination_cvc5_of_yojson "{}"]
    words : elimination_words;
        [@default Common.Util.config_default elimination_words_of_yojson "{}"]
    rewrites : elimination_rewrites;
        [@default Common.Util.config_default elimination_rewrites_of_yojson "{}"]
    pieces_first : elimination_pieces_first option; [@default None]
        (** during predicate elimination, [Some { z3_ms; cvc5_ms }] asks a
            validity question that splits into [ClausePieces] piece by piece
            before anything else: each piece natively under [z3_ms] ms
            (skipped for a shape the solver may not return on), then, when
            undecided and [cvc5_ms] is set, by cvc5 under that many ms; only
            proofs and refutations of pieces are read.  Every piece valid
            answers valid, a piece refuted answers invalid, and otherwise the
            question is asked whole by the usual route, so that the pieces
            can only add an answer, at the cost of their questions.  Sound: the question is the
            conjunction of its pieces in every model.  Why: the undecided
            resolvents of a Rust-derived loop are each a case split of a
            negated postcondition over several hundred shared premise
            disjuncts, which neither Z3 nor cvc5 decides whole in a minute,
            while cvc5 proves most of the cases in 0.1-0.4 s each.
            Off by default: over the Rust-derived inputs whose elimination
            asks such a question, [Some (1000, Some 3000)] lost no answer and
            took one input from two runs in three to three in three -- no
            input that only it answers -- while those runs took about 18%
            longer in total, since the pieces are asked before the whole
            question even where the whole question alone would have answered;
            on fixpoint-logic and transition-system inputs it acts on a few
            elimination questions and answered nothing the whole question did
            not.  [None]: every question asked whole *)
  }
  [@@deriving yojson]

  (** Predicate elimination by resolution: when an unknown is resolved away,
      how the clause set is kept small, and what is derived beside it.  Its
      validity questions are [questions]. *)
  type elimination = {
    resolution_threshold : int; [@default 4]
    bool_vars : int; [@default 0]
    complete : resolution_complete;
        [@default
          Complete_elimination
            {
              max_clauses = 100;
              prebound = false;
              early_exit = true;
              budget_ms = None;
              invalid_first_ms = None;
              skip_recursive = false;
            }]
        (** whether predicate elimination tries to resolve every unknown away
            when its threshold stops it (see [resolution_complete]) *)
    max_growth : int option; [@default None]
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
    subsume : elim_subsume;
        [@default Subsume { impl = Persistent; resolution_index = true }]
        (** whether predicate elimination drops subsumed clauses, and how (see
            [elim_subsume]) *)
    tautology_test : bool; [@default true]
        (** during predicate elimination, drop an input clause that is valid by
            a cheap syntactic test -- a head literal equal to a body conjunct,
            or two complementary disjuncts, an atom compared after
            [Evaluator.simplify] and [Normalizer.normalize] -- before its normal
            form is built, and a normal-form clause with an atom on both sides
            or complementary pure disjuncts.  Exact: a valid clause constrains
            nothing.  Such clauses are generated as obligations restating a
            body conjunct, and each is a negative occurrence of every predicate
            of its body. *)
    assign_before_cnf : bool; [@default true]
        (** during predicate elimination, substitute the constants the one-sided
            and bound steps assign (no positive or no negative occurrence, a
            valid lower bound, an unsatisfiable upper bound) into the input
            formulas and build the normal form again, instead of applying them
            to the normal form, whose copies of a disjunction around the
            assigned predicate are then already built.  Exact: the normal form
            of the substituted formulas is the substitution applied to the
            normal form, up to propositional simplification; the other
            definitions are found again on the rebuilt set. *)
    merge_definitions : bool; [@default false]
        (** during predicate elimination by resolution, merge the defining
            clauses of the predicate being resolved whose atoms carry the same
            predicates with the same signs into one clause, with the clauses'
            argument equations and pure parts as a conjunction in its pure part
            ([PvarEliminator.MergeDefs]).  Exact (one-point rule and
            distributivity), and it turns [pc * nc] resolvents into [nc] when
            the [pc] definitions are one per path of a conditional: without it,
            each such elimination splits every using clause per path, every
            predicate defined from them inherits the split, and the clause
            count is exponential in the nesting of conditionals (a 20-line
            program with three calls in one assertion did not leave
            elimination in 240 s).  On for the refinement-type checker's own
            elimination, whose threshold is unbounded; off elsewhere until
            measured there *)
    drop_derived_premises : bool; [@default false]
        (** in the predicate eliminator, after each resolution step, drop a
            premise [p(t)] of a clause when a definite clause of the set,
            under a substitution for its own variables, has the head [p(t)]
            and only premises and pure disjuncts the clause has
            ([ClauseOld.drop_derived_premises]).  Exact: given that clause, the
            clause with and without the premise hold in the same
            interpretations.  Only premises of predicates the eliminator may
            eliminate are dropped: a protected predicate's defining clauses
            belong to the caller, which may discard them (a game solver's
            strategy placeholders), and that voids a drop they licensed.  Wanted where a callee's precondition reaches
            each return site as a premise beside the call site's own context,
            and resolving it away later copies every call site's context into
            every return site.  Off by default: no input is known that needs
            it (on 127 Thrust inputs at 120 s it answered 68 runs against 67,
            the one difference a file also answered without it, and on one
            input the complete elimination it feeds took 886 s against 15 s);
            [false]: premises kept *)
    one_sided_fn_preds : bool; [@default false]
        (** replace a functional predicate that every clause uses only as a
            premise, at distinct variables, by an existential over its result.
            Equisatisfiable, but it removes the predicate without being able to
            define it, so a [sat] model no longer mentions it and the solution
            checker can only report that constraint unchecked -- off by default
            because measuring it found no verdict it earns and five models it
            stops being able to check *)
    fn_feeding_fn : bool; [@default false]
        (** drop a functional body atom (a witness of a skolemised body
            universal) whose result variable occurs only as a whole input
            argument of other functional body atoms, each applied once in the
            whole problem and each taking all of the dropped atom's inputs
            ([PCSP.Problem.elim_fn_feeding_fn_predicate], where the
            equisatisfiability is argued in both directions).  It is the shape
            left when the unknown the outer witness was for has been
            eliminated.  Asks no solver.  [false]: no such step *)
    fn_totality_consequences : bool; [@default true]
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
    set_aside : elimination_set_aside;
        [@default Common.Util.config_default elimination_set_aside_of_yojson "{}"]
    dedup_alpha_disjuncts : bool; [@default true]
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
    widest_first : bool; [@default false]
        (** predicate elimination by resolution chooses, among the candidates
            whose resolution duplicates no clause (one positive or one
            negative occurrence), the one of most arguments first, and only
            then the one whose resolution builds the fewest clauses; the same
            order among the other candidates.  Sound and complete as the
            default order is: every resolution step is equisatisfiable
            whichever unknown it removes; only which unknowns survive
            changes.  Wanted where a cycle of unknowns carries a
            well-foundedness reduction's record (a Boolean saying whether a
            state was recorded, and that state) on every unknown but its
            head: resolving the record carriers away leaves the head, whose
            well-foundedness obligation then reads the step directly, where
            the default order resolved the head (it builds fewer clauses) and
            left a record carrier, whose invariant has to describe the
            record's dummy initial state as well.  [false]: fewest clauses
            built first, most arguments only breaking ties *)
    speed : elimination_speed;
        [@default Common.Util.config_default elimination_speed_of_yojson "{}"]
    questions : elimination_questions;
        [@default Common.Util.config_default elimination_questions_of_yojson "{}"]
  }
  [@@deriving yojson]

  (** The merge-pattern prune of the pure condensation's search. *)
  type condensation_merge_pattern = {
    prune : bool; [@default true]
        (** with [condensation.pure.resolvents], fail a condensation search call
            at once when a touched disjunct can have no acceptable image under
            any completion of its bindings ([ClauseOld.condense_pure
            ~merge_pattern_prune]): its normal forms under every merge pattern
            of its variables (at most 256 patterns) have bags no live disjunct
            free of the domain has, and none is [false].  Rests on one
            assumption about the simplifier and normaliser: an injective
            renaming of free variables changes only names and operand order
            ([ClauseOld.condense_premise_ok]).  Under it the search returns
            what it returns without the prune wherever no budget cuts it; the
            result is an equivalence of the clause either way.  For a
            datatype decomposition tree copied into a resolvent, whose root
            disjunct holds every child variable and was found to have no image
            only after every combination of its variables' candidates.  On
            by default since 2026-10-21 (exact under that assumption, which
            the maintainer accepted; checked on 248,000 real formulas), with
            [condensation.pure.merge_pattern.gate].  Process-wide (the last value
            set wins) *)
    gate : int; [@default 2_000]
        (** with [condensation.pure.merge_pattern.prune], ask its test only once
            the condensation call has charged this many normalisations
            ([ClauseOld.condense_pure ~merge_pattern_gate]); 0 asks it in
            every search call.  A cost gate: on Thrust inputs the calls either
            end under 2,000 normalisations or reach the 20,000 cap, and the
            ungated test made the first kind 2-2.5 times as slow.  Exactness
            is unchanged.  Process-wide (the last value set wins) *)
  }
  [@@deriving yojson]

  (** The shape restriction of the pure condensation's candidates. *)
  type condensation_shape = {
    candidates : bool; [@default true]
        (** with [condensation.pure.resolvents], bind a variable of the search
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
    commutative : bool; [@default false]
        (** with [condensation.pure.shape.candidates], also let a variable line
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
  }
  [@@deriving yojson]

  (** The joint condensation of a resolution step's resolvents. *)
  type condensation_joint = {
    condense : bool; [@default true]
        (** with [condensation.pure.resolvents], let the condensation of each
            resolvent's pure part also drop a set of atoms together with the
            disjuncts over their variables, under one substitution mapping the
            atoms onto kept atoms of their polarity and the disjuncts onto kept
            disjuncts ([ClauseOld.condense_pure ~joint]); exact (the clause is
            equivalent to the result in every model).  For a straight-line
            chain of contexts each premising every earlier one, whose
            eliminations otherwise double each use's atoms and constraints.
            Process-wide and only ever turned on. *)
    prune_doomed : bool; [@default false]
        (** with [condensation.pure.joint.condense], stop enumerating a partial closure of
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
  }
  [@@deriving yojson]

  (** The condensation of the pure parts of resolvents (a variable merged
      into another when the clause stays equivalent), its search and its
      bounds. *)
  type condensation_pure = {
    resolvents : bool; [@default true]
        (** in the predicate eliminator, after [condensation.resolvents], condense
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
    min_side_size : int option; [@default None]
        (** a pre-check of [condensation.pure.resolvents], decided per
            elimination before any resolvent is condensed: with [Some f], the
            resolvents of eliminating a predicate are condensed only when the
            largest pure part among its defining clauses and the largest
            among its using clauses both have at least [f] nodes and the
            smaller of the two is at least half the larger, so that the step
            multiplies the larger pure part by at least 1.5.  That is the
            shape condensation is for: a chain of definitions each carrying
            every earlier one, where both sides of a resolution step hold a
            copy of the same constraints and the pure part doubles with each
            predicate eliminated.  A step whose use side is small adds a few
            constraints to a definition and copies nothing; a skipped step's
            copies stay in its resolvents and are condensed when a later step
            that passes the test resolves them, so the condensation is
            delayed, not lost, wherever the chain goes on growing.  Asks
            nothing, so the result is exact either way.  [None]: every
            elimination condenses its resolvents, as before *)
    unknown_free_resolvents : bool; [@default false]
        (** with [condensation.pure.resolvents], condense also a resolvent that
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
    max_checks : int; [@default 20_000]
        (** with [condensation.pure.resolvents], the number of normalisations one
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
    max_search_nodes : int option; [@default None]
        (** with [condensation.pure.resolvents], the number of search calls one
            condensation of a resolvent may make, over all its seeds
            ([ClauseOld.condense_pure ~max_search_nodes]); past it the search
            stops and the resolvent keeps the condensations found so far,
            still an equivalence.  [None]: no bound.  Why: the normalisation
            budget below does not bound the search, since an image already
            normalised costs no check, and on a Thrust input with arity-27
            loop invariants one condensation backtracked through cached images
            for more than two minutes, the rest of the run's 300 s; a bound
            per seed did not stop it, the resolvent having hundreds of seeds *)
    memo_failures : bool; [@default true]
        (** with [condensation.pure.resolvents], remember each failed call of the
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
    cbag_memo : bool; [@default true]
        (** with [condensation.pure.merge_pattern.prune], compute the bags of the
            prune's pattern images and disjuncts through a per-call table
            keyed up to an injective renaming of the free variables a bag
            erases ([ClauseOld.condense_cbag_memo]).  Exact: the same bags,
            questions and fresh names.  Process-wide (the last value set
            wins).  Why: on a Thrust coroutine input two thirds of the
            condensation of three resolvents of about 2,000 disjuncts each
            went into printing the bags of renamed images *)
    pattern_memo : bool; [@default false]
        (** with [condensation.pure.merge_pattern.prune], remember across the
            calls of [ClauseOld.condense_pure] in a domain what the prune reads
            of each pattern image (whether its normal form is false, its
            occurrence profile, its bag), keyed by the disjunct, the renaming
            and the binder-renaming mode ([ClauseOld.condense_pattern_memo]).
            Exact: the same condensation, normalisations charged, search calls
            and fresh names.  Process-wide (the last value set wins).  Off by
            default: on Rust-derived inputs whose condensation is their open
            phase it cut the condensation's time by at most a quarter, within
            the run-to-run spread on most of them, answered no further input,
            and raised the peak resident size from about 0.5 GB to 0.9-1.6 GB *)
    merge_pattern : condensation_merge_pattern;
        [@default Common.Util.config_default condensation_merge_pattern_of_yojson "{}"]
    shape : condensation_shape;
        [@default Common.Util.config_default condensation_shape_of_yojson "{}"]
    inclusion : bool; [@default true]
        (** with [condensation.pure.resolvents], bind a variable [u] of the search
            only to a variable [y] of an inclusion relation computed once per
            pass over a resolvent, in place of the printed alignment of
            [condensation.pure.shape.candidates]
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
    joint : condensation_joint;
        [@default Common.Util.config_default condensation_joint_of_yojson "{}"]
  }
  [@@deriving yojson]

  (** Condensation: a clause replaced by an equivalent one with fewer
      variables or literals, on resolvents and on the final clauses. *)
  type condensation = {
    resolvents : bool; [@default true]
        (** in the predicate eliminator, condense every resolvent: drop a
            literal that another literal of the same polarity and clause is an
            instance of, by a substitution for variables occurring nowhere
            else in the clause.  An equivalence of the clause (the argument is
            at [ClauseOld.condense]).  Where [elimination.drop_implied_body_atoms] removes
            such a premise once from the final clauses, this removes it from
            each intermediate resolvent too, so a copy sitting on a predicate
            that is eliminated later is gone before that elimination resolves
            it, and the occurrence counts the elimination rules decide from
            never see one premise twice.  It changes the clause set every
            later phase sees, which is why it waited for a corpus sweep
            before becoming a default *)
    final_clauses : bool; [@default false]
        (** after the other passes, condense every clause once more
            ([ClauseOld.condense]: drop a literal of which another literal of
            the same polarity is an instance by a substitution for variables
            occurring nowhere else in the clause, integer arguments compared
            up to their linear normal form).  An equivalence of each clause.
            Wanted with [clauses.split_single_cons]: once a tuple's fields
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
    final_unknown_free : bool; [@default true]
        (** at the end of preprocessing, rewrite a clause that applies no
            unknown by four equivalences, in this order: cancel the common
            prefix and suffix of each sequence equation
            ([Evaluator.cancel_seq_concat_equations]), apply each equation
            between two variables of one sort as a renaming
            ([ClauseOld.merge_var_equations]), rename the bound variables of
            each quantified disjunct canonically, so that two copies of one
            quantified premise are spelled alike, and condense the clause's
            disjuncts ([ClauseOld.condense_pure], then repeats dropped).  Each step is an
            equivalence of the clause in every model.  Only a clause that,
            once cancelled, equates two variables of a sort other than [Int]
            is rewritten ([PvarEliminator.UnknownFreeCondense]), since the
            ladder's route depends on a clause's form and condensing every
            atom-free clause cost three inputs their answers.  Why: a loop step whose
            context is stated twice -- by the loop head's own unknown and
            again through the unknown of the call inside the body -- reaches
            the zero-unknown verdict with every existential fact of the loop
            invariant skolemized once per copy, the copies tied only by
            [p ++ x = p ++ y]; each copy brings its own case splits, so the
            ladder split the step into four times as many pieces *)
    unknown_free_resolvents : bool; [@default false]
        (** the rewriting of [condensation.final_unknown_free], applied
            by the predicate eliminator to each resolvent that applies no
            unknown as soon as it is built, before the resolvent's
            simplification asks whether it is valid.  An equivalence of the
            clause in every model, as there.  Why: a loop step whose context
            is stated twice reaches the eliminator's validity questions with
            every skolemized fact of its invariant once per copy, so each
            question carries both copies; condensed first, it carries one *)
    up_to_linear : bool; [@default false]
        (** let condensation compare integer subterms up to their linear
            normal form, also inside constructor applications
            ([ClauseOld.condense_up_to_linear]); off, they must be
            syntactically equal.  Exact either way.  Wanted with
            [clauses.split_single_cons], whose resolvents keep a premise
            copy whose only difference from the kept premise is [-1 + x]
            against [-(1 - x)].  Set process-wide when a solve starts *)
    unify_negated_linear : bool; [@default false]
        (** let the unifier that resolution and the clause graph use solve a
            negated linear term ([-(1 - x)] and its siblings) for its
            variable ([LogicOld.unify_negated_linear]); off, such a term
            matches only itself.  Sound either way.  Wanted with
            [clauses.split_single_cons]: the fresh field names it
            introduces change which side of a linear equation the elimination
            solves, and the loop step [p x => p (x + 1)] came out as
            [p (-(1 - y)) => p y], which no positive example unified with, so
            no example was resolved forward through it.  Set process-wide
            when a solve starts, also for the solving loop after it *)
    pure : condensation_pure;
        [@default Common.Util.config_default condensation_pure_of_yojson "{}"]
  }
  [@@deriving yojson]

  type finite_nested_solve =
    | No_nested_solve  (** an instance the single query leaves undecided stays undecided *)
    | Nested_solve of {
        budget_ms : int option; [@default Some 10000]
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
        strict_budget : bool; [@default true]
            (* enforce the budget above inside a phase too: the synthesizer's retry
               loop yields once it has passed, and each of its solver calls is capped
               by the time left.  Off, a synthesis step that keeps failing can hold a
               nested solve far past its budget -- measured: ten seconds granted, still
               running after 150, the main solve never started. *)
        stage_deadline : bool; [@default false]
            (* also read the nested solve's strict deadline at the stage boundaries
               before the CEGIS loop's first phase -- the qualifier generator's loops
               over predicates and clauses, the building of the phases and the
               synthesizer's initialisation -- and end the nested solve there once it
               has passed, as an undecided size.  Without it the strict budget is read
               only inside the synthesizer's retry loop and the labeling, so building
               the first templates is unbounded: on a Thrust input of about a hundred
               clauses after elimination the nested solve given ten seconds spent
               about 500 s extracting qualifiers (83,499 instantiations) before its
               first synthesis query, and the main solve never started.  Only a
               refutation crosses from the nested solve, so this can lose a
               refutation found after the budget and changes no other answer. *)
        after_first_round_ms : int option; [@default Some 2000]
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
        fresh_context : bool; [@default true]
            (* run each nested solve above on a solver context of its own, cleared
               before it and restored after it, where the caller supplies such a
               solver (the constraint solver's own entry point does).  The context
               carries the example graph and truth tables from one solve to the next,
               and without this the MAIN solve started from the nested solve's
               examples about the instance: on one input whose instance is satisfiable
               in 0.3 s the main solve then answered 0 of 8 across four builds where
               with the nested solve off it answered 5 of 8.  Removing inherited
               examples can only remove premises a refutation might rest on. *)
      }  (** such an instance handed to a nested solve, with these parameters *)
  [@@deriving yojson]

  type finite_forall_sorts =
    | No_finite_instances  (** every quantified sort is left as it is *)
    | Instantiate of {
        by_name : bool; [@default true]
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
        targeted : bool; [@default true]
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
        max_instance_size : int option; [@default None]
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
        query_timeout_ms : int; [@default 2000]
            (* the budget in milliseconds of the single solver call deciding each size
               before the nested solve is tried.  Bimodal in the same census: the
               18 decided calls all returned within 0.12 s, while of the 28 undecided
               ones 21 gave up at once and 7 spent the whole
               budget (it was 10 s, which was most of a satisfiable input's time before
               its main solve began -- the nested solve after it then took 0.5 s).
               A call that times out hands the size to the nested solve, which decides
               it too when it can. *)
        fork_query : bool; [@default true]
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
        charge_construction : bool; [@default false]
            (* charge building a size's instance to [finite_forall_sorts.query_timeout_ms]:
               the budget is a deadline from the start of that size, read between the
               construction's steps (the sort substitution, each round of the
               finitising loop and each step in it), and the query gets what is left.
               Past it the size is answered [Timeout] exactly as the query running out
               is today, so the nested solve, with its own budget, is still tried.  A
               single step that does not return, or the conversion of the finished
               instance for the solver, is not cut short.  Off (the default) the budget
               covers the solver call alone, and building the instance is unbounded.
               Sound for the same reason as above: only a refutation transfers. *)
        parallel : bool; [@default false]
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
        nested : finite_nested_solve;
            [@default Common.Util.config_default finite_nested_solve_of_yojson {|["No_nested_solve"]|}]
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

               Off by default: no answer was found that needs it.  Over the 42
               dependently quantified files that declare a quantified sort (one binary,
               this field the only difference, 90 s): 0 verdict disagreements, 31
               answered on each side, on 1.07x wall; the one input that answered only
               with it answered a wrong `unsat` reached through the array-literal
               equality above (its two-element instance is satisfiable), which the
               rewrite removes.  Over 367 quantified-sort files at 120 s, three runs
               each where it acts, turning it off gained answers net, no wrong answer,
               the runs taking 0.78 of the time; on the Rust-derived inputs where it
               acts, the same answers in less time.

               What the measurement does not cover, because no input in it has the
               shape: a caller that runs two constraint-solving calls at once, each
               reaching this pass.  The environment swap below is a blind overwrite,
               so two such calls would silently take each other's datatypes.  That
               hazard is not this switch's -- the pass above installs the same
               environment for its own query and is on by default -- but this switch
               lengthens the window from one query to a whole nested solve. *)
      }  (** each quantified sort instantiated at finite sizes, with these parameters *)
  [@@deriving yojson]

  (** Which Z3 contexts the unfolding refutation's questions are asked in.
      Each resolvent is asked in a forked copy of the process, which inherits
      the process's pooled contexts with everything earlier questions left in
      them (declarations, the solver having been pushed); a pooled question's
      answer can then depend on which questions the process asked before the
      fork, and identical question texts were answered differently in two
      runs whose histories differed. *)
  type unfold_contexts =
    | Inherited_contexts
        (** the contexts the copy inherits from the process, as any question
            of the process would be asked *)
    | Cleared_contexts
        (** the copy drops every pooled context it inherited before its first
            question ([Z3interface.clear_instance_pool]), so that each of its
            questions is asked in a context made inside the copy: the answers
            are a function of the resolvent and of the copy's own earlier
            questions, not of the process's history.  The questions and the
            reading of their answers are unchanged; the cost is one new context
            (and its forced collection) per pooled configuration per resolvent *)
    | Cleared_fresh_native
        (** as [Cleared_contexts], and the question asked natively (the
            validity question where no sequence length is guessed) is asked
            in a context of its own ([fresh_solver:true]) rather than in a
            pooled one, as the relaxation and the pinned negation already
            are *)
  [@@deriving yojson]

  type refute_by_unfolding =
    | No_unfolding  (** no refutation by unfolding *)
    | Unfold of {
        depth : int; [@default 12]
            (** the levels of the unfolding above: with
                [refute_by_unfolding.linear] [d] levels cover chains of up to [d]
                facts, without it a two-atom step doubles the formula per level
                and [d] levels cover chains of up to [2^(d-1)] *)
        counter_depth : int option; [@default Some 128]
            (** with [Some c], an unknown whose clauses carry a bounded counter
                (an integer argument that every fact sets to a literal [s], that
                every step, each with one body atom, increments by one under a
                guard [v < b]) is unfolded to the [b - s + 1] levels the counter
                allows, when that is deeper than [refute_by_unfolding.depth], at
                most [c] ([UnfoldRefute.counter_depth]); the size bound grows by
                the same factor.  A goal that needs the counter at its bound is
                reached at exactly that depth: on a loop counting the 64 bits of
                a word, the refutation needs 65 levels, where the default depth
                reaches 12.  Only the depth changes, so soundness is not at stake;
                it costs the larger unfolding on every input with such a
                counter, refutable or not. *)
        solve_linear : bool; [@default true]
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
                [refute_by_unfolding.hoist_bounds] Z3 fixes it by propagation
                (refuted in about 2 s, where neither switch alone nor the default
                decides it within the step budget). *)
        hoist_bounds : bool; [@default true]
            (** before a resolvent is asked, the integer bounds its negation
                implies -- read through conjunction (intersection), disjunction
                (hull) and quantifiers ([BoundHoist.implied_bounds]) -- are made
                top-level conjuncts of the negation.  Exact (a formula is
                equivalent to its conjunction with what it implies); it puts the
                range of a word that every disjunct of an unfolding bounds where
                [z3.int_to_bv]'s bounded rule reads ranges, and the
                counter's range where Z3's propagation fixes it. *)
        linear : bool; [@default true]
            (** unfold only the first body atom of a step through the lower level
                and put the facts at the others, so that a level adds one copy of
                the level below.  The doubling form reached the same chain at
                depth 5 with a formula Z3 decided in no budget tried (up to 60 s
                on three seeds), where the linear one at depth 11 was decided in
                7 s *)
        timeout_ms : int; [@default 30000]
            (** the budget of each solver question of the unfolding above (at
                most three per resolvent): a resolvent is asked in a forked copy
                killed after three times this, since Z3's own timeout does not
                bound these questions over sequences *)
        budget_ms : int; [@default 60000]
            (** no resolvent is asked about once this much time has passed since
                the unfolding started, and the copy asking one is killed when it
                is reached *)
        max_size : int option; [@default Some 20000]
            (** with [Some m], an unknown whose unfolding has a level of more than
                [m] nodes gets none, and a resolvent of more than [m] nodes is not
                asked about ([UnfoldRefute.size_up_to]), so that the unfolding
                costs little on an input it cannot refute *)
        step_ms : int option; [@default Some 10000]
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
        fitting_doubling : bool; [@default true]
            (** when the unfolding above refutes nothing and its budget is not
                spent, a second pass over the same clauses in the doubling form
                (every body atom of a step unfolded through the level below,
                [refute_by_unfolding.linear] notwithstanding), up to
                [refute_by_unfolding.depth] levels, that keeps the levels below
                the first one over [refute_by_unfolding.max_size] and asks each
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
        exact_levels : bool; [@default true]
            (** when the first pass above refutes nothing and the budget is not
                spent, before the doubling pass, ask each goal whose resolvent has a free sequence against
                the derivations of exactly [k] levels, [k = 1, 2, ...] up to
                [refute_by_unfolding.depth] within [refute_by_unfolding.max_size]
                ([PCSatCommon.UnfoldRefute.refute_exact_levels]), with the same
                questions, budgets and kill.  Sound for the reason the first pass
                is, and it never concludes [sat].  What it reaches: a refutation
                the first pass's length guess misses because its relaxation,
                read against every derivation of up to [depth] levels at once,
                gives a free sequence the length of the wrong derivation -- a
                loop's history of visited items pinned empty, where a wrong
                count is still right, or pinned at the deepest level, which the
                solver does not decide within the step's budget.  [false] asks
                nothing more.  Bounded by [exact_levels_budget_ms] and
                [exact_levels_step_ms] below, not by the first pass's step:
                with that step and the rest of the pass's 60 s, it spent 49 to
                59 s on each of seven satisfiable Thrust inputs it could not
                refute, and four of them lost their answer at 120 s. *)
        exact_levels_budget_ms : int; [@default 15000]
            (** the whole budget of the [exact_levels] pass, within what is left
                of [refute_by_unfolding.budget_ms] *)
        exact_levels_step_ms : int; [@default 3000]
            (** the budget of each of the [exact_levels] pass's questions, the
                relaxation that guesses the lengths and the pinned negation
                alike.  The refutation it was written for answers in 0.5 s at
                the third level, after a second level that is not decided in
                10 s *)
        guess_ms : int option; [@default None]
            (** with [Some n], the relaxation above that guesses the sequences'
                lengths is killed after [n] ms ([UnfoldRefute.ask]'s
                [guess_ms]), and a resolvent whose relaxation is killed is left
                undecided.  It loses only refutations whose relaxation takes
                longer than [n] ms.  On a satisfiable Thrust input the relaxation
                (3,000 nodes, quantifier-free over sequences) ran until the
                pass's 60 s kill, which was the whole cost of the pass; the
                refutation the pass is kept for takes 7 s there.  [None]: bounded
                by the pass's budget only. *)
        guess_retries : int; [@default 0]
            (** when the sequences' lengths guessed by the relaxation give a
                pinned negation with no countermodel, exclude those lengths
                from the relaxation and guess again, up to this many more
                times ([UnfoldRefute.ask]'s [guess_retries]).  The relaxation
                drops the quantified parts of the negation, so its model can
                fix a length that no countermodel has, and one guess is one
                draw: on a Rust-derived iterator input the guess put one
                element in a visited prefix the refutation needs empty in about
                one run in four, and the pass then refuted nothing.  It only
                asks more questions, under the same budgets; [0] guesses once *)
        fn_steps : bool; [@default true]
            (** also unfold a step whose body holds, beside the unknown's own
                atoms, atoms of FUNCTIONAL unknowns whose results are variables
                read nowhere else but in the unknown's atoms (not in the head,
                the pure part or another functional atom): the level reads the
                step with those results universally quantified,
                [forall v. /\_j L(b_j)] ([UnfoldRefute.fn_results]).  Sound
                by totality alone: whatever value the witness takes, the body
                atoms hold there.  Such a step is what a premise
                [forall q. P(..q..)] becomes once the reader skolemises [q]
                into a functional witness, and without it the unfolding never
                reads the step, so a refutation through it is left to the
                CEGIS loop, where the witness's value and the other free
                values of each counterexample are fixed by the solver and the
                examples never meet.  [false]: such a step is not read.  On
                by default: it reached 11 of 901 inputs, refuted a Rust-derived
                iterator's unsatisfiable input the CEGIS loop never answered,
                and moved the solves of the other ten by under 2 s *)
        parallel : bool; [@default true]
            (* run the unfolding refutation ([refute_by_unfolding], with its doubling
               pass) in a forked copy raced against the rest of the run, as
               [finite_forall_sorts_parallel] does for the finite instantiation, and
               for the same reason: the pass only refutes, so the copy answers only
               with the refuted problem and continues from there as the sequential
               order would, while the process goes on at once with the problem as
               given.  Its verdicts are the sequential order's: a process [sat]
               means there was no refutation to find, an [unsat] is the same
               verdict, and any other answer (an [unknown], an error) waits for
               the copy until the pass budget ends before the copy is killed, so
               a refutation found within that budget is still printed.  What is
               not the same is time: on inputs it does not refute the pass spends
               its budget (10-60 s, one or two questions killed at [step_ms], or
               the length guess killed at [budget_ms]) beside the run instead of
               before the CEGIS loop and the raced Houdini copy start; a
               refutation near a wall-clock bound can be cut by the copy sharing
               cores with the run.  Raced under the same conditions as the finite
               instantiation (a place to leave the race, no deadline-bounded
               solve); elsewhere it runs in its sequential place.  [false]:
               always in its sequential place. *)
        contexts : unfold_contexts; [@default Inherited_contexts]
            (** which Z3 contexts each resolvent's questions are asked in (see
                [unfold_contexts]) *)
      }  (** the refutation by unfolding, with these parameters *)
  [@@deriving yojson]

  type argument_reduce =
    | No_arg_reduction  (** no unknown loses an argument here *)
    | Reduce of {
        keep_sequences : bool; [@default true]
            (** with [argument_reduction.reduce], never erase an argument of sequence sort
                ([DimReducer.keep_sequence_args], where the reason is given): a
                ghost history threaded through a loop and read by no constraint
                is erased otherwise, and the loop's invariant, quantifier-free
                over the history, becomes an existential over it that no template
                or candidate atom states.  Keeping an argument never loses a
                solution; on the Rust-derived inputs measured it changed the
                reduction only on loops with such a history, which it made answer.
                [false]: every argument may be erased *)
      }  (** the unused arguments of the unknowns dropped *)
  [@@deriving yojson]

  type share_determined =
    | No_share_determined  (** no argument shared *)
    | Share_determined of {
        budget_ms : int option; [@default None]
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
        seq_axiom_fallback_ms : int option; [@default None]
            (** the cap on the sequence-axiom fallback (the second attempt at an
                undecided validity question over sequences) inside the pass above,
                as [elimination.questions.seq_axiom_fallback.cap_ms] is for the predicate
                elimination: [None] leaves the process-wide budget as it is,
                [Some 0] (or less) asks no fallback there, [Some n] at most [n] ms.
                The fallback can only turn an undecided answer into [`Valid], so
                not asking it can only drop a candidate equality the pass would
                have kept: cost and completeness, never soundness.  On the input
                above nine fallbacks took 28.8 s, of which Z3 4.7 s. *)
        syntactic_first : bool; [@default true]
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
                leaves one undecided the two forms can keep different sets (a
                syntactic proof or a decided conjunction keeps an equality the
                one-by-one question left undecided; a remembered undecided answer
                is not asked again), every kept equality proved inductive either
                way, so both results are sound sharings.  On inputs where the
                pass asks Z3 at all, the problem preprocessed with the switch was
                the one preprocessed without it (up to fresh names) wherever the
                preprocessing is repeatable, and the pass asked a fraction of the
                questions (170 of 1,309 on one input). *)
        memo_questions : bool; [@default true]
            (** in the pass above, ask each distinct question once it has been
                decided: a question equal (after the simplification every
                question gets) to one the pass has already decided with the same
                time limit takes that answer; an undecided one is asked again.
                Every question asked is one the pass without the switch asks, in
                the same order; what the switch removes is the second and later
                asking of a decided formula under the same limit, which the pass
                makes when several candidates of one head atom denote the same
                equation (the atom repeats an argument) and when a residual of one
                candidate is asked first as a one-element conjunction and then
                alone.  Exact: a valid or invalid answer is a fact about the
                formula, a candidate is kept exactly when its question (or a
                conjunction holding it) is answered valid, and a countermodel
                drops only candidates that are invalid, whichever countermodel it
                is; so the kept set is the one without the switch wherever the
                repeated asking decides as the first did, and otherwise holds a
                candidate proved valid that the repeat would have left undecided.
                On by default, being exact.  Why: on a Thrust closure input 737
                of the pass's 1,309 askings repeated an earlier question *)
        memo_undecided : bool; [@default false]
            (** with [memo_questions], keep the undecided answers too: a
                question equal to one already left undecided under the same
                time limit is answered undecided without asking again.  The
                repeats come from the candidate list itself: a pair of leaves
                of the same sort is a candidate in both orientations ([x = y]
                and [y = x], which the simplification makes one formula), and
                both are needed, since each covers the leaf on its own left
                side; an atom that repeats an argument adds more.  Not exact:
                a second asking of an undecided question can decide it (a
                pooled solver context that has worked on it is not a fresh
                one), and with the switch it is not asked, so the pass can keep
                fewer equalities; never more, since only an undecided answer is
                reused and an undecided question keeps nothing.  Sound either
                way.  Why: on a Rust-derived closure input whose premises are
                quantified over sequences, 30 of the pass's 86 askings repeated
                an undecided question (each undecided again), at about 2.7 s
                each, the solver's 2 s and the sequence-axiom fallback *)
        slice_questions : bool; [@default false]
            (** with the switch above, first ask the conjunction of the
                candidates the syntax leaves on the premises connected to their
                variables only ([ClauseCone.slice]), keeping them all when that is
                proved (a proof of the slice is a proof of the whole question,
                whose premises it drops) and going on as above otherwise.  On the
                Thrust input it was built for the slices kept 58% of the premises
                and none was proved, so each cost one question more. *)
        unseen_vacuity : bool; [@default true]
            (** in the pass above, a candidate equality one of whose sides is a
                variable (or a field of a record variable) the clause's premises
                cannot see ([ClauseCone.unseen_var]: it occurs in no premise; it
                is an integer-indexed array read only at indices whose binder's
                body has a fixed truth value at index -1; or only premises about
                it alone mention it and they admit two values) is asked as the
                question whether the premises are unsatisfiable, once per clause
                and round, instead of once per candidate.  The two questions are
                equivalent: in any model of the premises the variable can be
                changed so that the equality fails and no premise does, so the
                equality follows from the premises exactly when nothing does.
                Where the solver decides both, the pass keeps exactly what it
                keeps without the switch.  On a Thrust input whose head arrays
                are constrained only on a range, 132 of the pass's 137 questions
                were such equalities, each undecided at its 2 s; with the switch
                the pass asks 55 (15 of them the clauses' unsatisfiability) and
                takes 152 s against 452 s. *)
        collections_only : bool; [@default false]
            (** a pre-check of [share_determined], decided from the
                unknowns' signatures before any question: an unknown is a
                candidate of the pass only when a leaf of one of its arguments
                has a sequence or array sort and a part of another argument has
                the same sort; its candidate equalities are then all kept,
                whatever their sorts, since the inductive subset is a fixpoint
                over all of them.  Why: what dropping a determined argument buys
                is in the array template, where a copied sequence -- a mutable
                reference whose current and final values are also fields of a
                tuple argument -- doubles the integer index columns the cell
                guards are counted by, and dropping the copy brought a loop head
                back under that bound (a Rust-derived loop over a vector answered
                in five runs of five instead of none).  An unknown whose
                arguments share no sequence or array has no such columns to
                save, and there the pass only asks its questions and changes the
                signature the learner sees.  [false]: every ordinary unknown of
                two or more arguments is a candidate, as before *)
      }  (** the arguments other arguments determine shared, with these parameters *)
  [@@deriving yojson]

  (** The reduction of the unknowns' arguments: unused arguments dropped,
      arguments determined by others shared, constant and copied arguments
      dropped. *)
  type argument_reduction = {
    reduce : argument_reduce;
        [@default Common.Util.config_default argument_reduce_of_yojson {|["Reduce", {}]|}]
    share_determined : share_determined;
        [@default Common.Util.config_default share_determined_of_yojson {|["Share_determined", {}]|}]
        (** drop an argument of an ordinary unknown when the clauses force
            every part of it to equal a part of another argument, and keep the
            forced equalities as a conjunct of the unknown's definition
            ([share_determined] below).  An argument that is a copy
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
  }
  [@@deriving yojson]

  (** The physical sharing the preprocessing passes keep: exact, the same
      formulas up to sharing. *)
  type sharing = {
    formulas : formula_sharing; [@default Rebuilt_formulas]
        (** how much physical sharing the passes that rebuild every formula of
            a problem keep (see [formula_sharing]).  [Rebuilt_formulas] by
            default, being exact: every output and fresh-name draw is the one
            [No_sharing] gives *)
    let_passes : bool; [@default true]
        (** inside [PCSP.Problem.normalize], the let passes (renaming let
            binders apart, putting lets in normal form, inlining lets whose
            definition applies an unknown) remember each node's result by
            physical identity under the same context, when computing it
            drew no fresh name; the same output, value for value and draw
            for draw, but shared where the input was.  On by default, being
            exact *)
    clause_dt_conversion : bool; [@default true]
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
    share_input : bool; [@default false]
        (** at the start of [preprocess], rebuild a raw problem's formulas
            maximally shared ([Common.DagShare.share]: every two structurally
            equal subformulas one block).  The same formulas as values; with
            the passes' address-keyed tables (which store a result only when
            computing it drew no fresh name) every output and draw is the one
            the unshared input gives, so it changes memory and time only.
            Why: an input built by a pass that substitutes without a table
            arrives as a tree whose distinct part is far smaller -- a
            termination problem converted from a 4.8 MB integer transition
            system reached the preprocessing as 6.5 million heap blocks for
            under 40 thousand distinct ones, and the passes' tables can keep
            sharing but not restore it.  Costs a full major collection and one
            walk of the input per call.  Off by default *)
  }
  [@@deriving yojson]

  type split_single_cons =
    | No_single_cons_split  (** no clause variable split *)
    | Split_single_cons of {
        selected_only : bool; [@default false]
            (** with [clauses.split_single_cons], split only a clause variable
                that the clause reads through a selector (and, recursively, only
                the fields that are read through one); a variable the clause only
                passes whole stays as it is.  Each split is the same identity, so
                this changes which equivalent clause is produced, never its
                meaning *)
        outside_upper_bound_probe : bool; [@default false]
            (** with [clauses.split_single_cons], leave the problem the
                solver's upper-bound definition probe solves unsplit (the
                input with some unknowns defined by candidate formulas), and
                split only the problems solved otherwise.  Each split is an
                equivalence, so this changes which equivalent problem the
                probe solves, never its meaning.  Why: on a Rust-derived
                input answered only through that probe, the split turned
                the probe's predicate-free questions into forms the
                zero-unknown stage did not prove within 400 s; with the
                probe's problem left unsplit it was answered in every run,
                and the inputs the split helps are answered on the main path *)
        outside_early_pins : bool; [@default false]
            (** with [clauses.split_single_cons], when the split acted, let
                the zero-unknown verdict's early relation pin, once it has
                searched the split clauses as without the option and found
                nothing, search the same input preprocessed again with the
                split left out (under a deeper solve depth and with the costly
                refuting stages skipped), under a fresh copy of the early pins'
                budget, with the fresh names it draws and the pooled contexts
                it uses kept apart from the rest of the run.  Sound: the split
                replaces a variable of a single-constructor datatype by its
                constructor applied to fresh field variables, an equivalence
                per clause, and every other pass keeps every refutation, so a
                countermodel of a clause of the unsplit problem refutes the
                input; the pin reads only countermodels.  Cost: a second
                preprocessing, as long as the first, on every run whose split
                acted and whose early relation pin finds nothing on the split
                clauses (every satisfiable input of this shape).  Why: on a
                Rust-derived input whose clause reads both fields of tuples of
                relation arrays, the split problem's shape guesses gave a
                relation at most seven tuples where the countermodel needs
                eleven, no pinned negation was a countermodel, and the run
                ended without an answer, where the unsplit clause was refuted
                by the early relation pin within 20 s *)
      }  (** a clause variable of a single-constructor datatype split into its fields *)
  [@@deriving yojson]

  type word_ranges =
    | No_word_ranges  (** no range invariant of a bit-vector word offered *)
    | Word_ranges of {
        timeout_ms : int; [@default 2000]
            (** the budget of each validity question of the pass above, asked in
                a forked copy killed at three times it *)
      }  (** the range invariants of bit-vector words offered, each checked under this budget *)
  [@@deriving yojson]

  (** How the clauses are prepared around the elimination: encodings,
      splits and rewrites of single clauses. *)
  type clauses = {
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
    eliminate_pointwise_sequence_existentials : bool; [@default true]
        (** replace an existential sequence of a clause, at positive polarity,
            that is read only through its length and through one guarded
            pointwise condition [forall q. 0 <= q < len s => B(q, s[q])] by an
            existential over its length, the condition becoming
            [forall q. 0 <= q < n => exists e. B(q, e)] (nothing at all when
            [B] defines the element as a term)
            ([Evaluator.eliminate_pointwise_defined_sequences]).  Exact in
            every model, so sound for both answers.  What it buys: a loop
            exit whose postcondition needs the produced sequence
            [[start, ..., start + c - 1]] as a witness, which no clause term
            denotes, no answer at 300 s with the sequence and [sat] with its
            length *)
    merge_concatenated_sequence_existentials : bool; [@default false]
        (** on a clause in which a sequence binder survives the rewrite
            above and the length-only elimination after it, merge two
            existential sequences, at positive polarity, that are read only
            through their lengths and their one concatenation [p ++ x] into
            one sequence standing for [p ++ x] and an integer standing for
            [len p]
            ([Evaluator.merge_concatenated_sequence_existentials]), the
            existentials of the block's [and]/[or] spine first moved to the
            block.  Exact in every model, so sound for both answers.  What it
            buys: the sequence a nested adapter's [produces] reads only behind
            its inner prefix ([q ++ s]) becomes one the rewrite above can
            replace by its length; that rewrite is run again on a merged
            clause.  Off by default *)
    dedup_alpha_equivalent_disjuncts : bool; [@default true]
        (** drop disjuncts of a clause that differ only in the names of their
            bound variables, which merging clauses that share a premise
            produces; runs before the instantiation above *)
    dedup_alpha_equivalent_clauses : bool; [@default false]
        (** as the last step of the preprocessing, drop a clause that differs
            from another only in the names of its bound variables
            ([PCSP.Problem.dedup_alpha_equivalent_clauses]); exact, the
            constraint set being the same.  Why: the elimination and the
            argument sharing can produce one clause several times with its own
            binder names each time, and each copy is then validated, labelled
            and resolved on its own: on a Rust-derived loop entry, seven copies
            of a goal clause made every validation round ask one undecided
            quantified question seven times at the full budget.  Off: the
            copies are kept. *)
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
    tester_normal_form : bool; [@default true]
        (** rewrite every tester-guarded selector read at negative polarity to
            a constructor equation over fresh clause variables: a premise
            [is_C t /\ psi[s_i t]] becomes [t = C(ys) /\ psi[ys]], [ys]
            universally quantified over the clause, for a datatype with at
            least two constructors ([Evaluator.tester_normal_form_free_vars]).
            An equivalence per clause in every model, whatever a selector off
            its constructor denotes, so sound for both answers.  What it buys:
            the two encodings of a payload a frontend may emit -- the
            constructor equation, or the tester and its selectors -- reach the
            solver as one, and the equation lets the clause's one-point rule
            substitute [t := C(ys)] so that every later read of [t] folds,
            where the selector form leaves the tester as a literal and every
            term built over the payload a selector term over [t].  A
            conclusion's [is_C t /\ ..] is left as it is.  Runs before the
            first per-clause simplification; a problem that arrives already
            clausified is left alone.  [false]: no such rewrite *)
    split_single_cons : split_single_cons;
        [@default
          Common.Util.config_default split_single_cons_of_yojson
            {|["Split_single_cons", {"selected_only": true, "outside_upper_bound_probe": true}]|}]
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
            sorts; a problem that arrives already clausified is left alone.  The
            default splits only the variables read through a selector, and
            not in the problem the upper-bound definition probe solves *)
    cancel_seq_concat_equations : bool; [@default false]
        (** after the predicate elimination and again before the final
            normalisation, rewrite every sequence equation and disequation by
            cancelling the common prefix and suffix of its two sides' operands
            ([a ++ x = a ++ y] to [x = y]), exact since concatenation is
            cancellative.  Meant for [clauses.split_single_cons], whose
            plain field variables let the elimination substitute definitions
            [v1 = v0 ++ v3] and so build equations [v0 ++ w = (v0 ++ v4) ++ v3]
            that Z3 decides far less readily than [w = v4 ++ v3].  Off by
            default although the split is on: with the split, it turned a
            Rust-derived unsatisfiable input answered in every run in 8 s
            into one answered in one run of four *)
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
    word_ranges : word_ranges;
        [@default Common.Util.config_default word_ranges_of_yojson {|["Word_ranges", {}]|}]
        (** before handing the preprocessed problem to the solver, find which
            integer arguments of the ordinary unknowns stay in
            [[0, 2^n)] for a width [n] some [int_to_bv n] of the problem
            uses (the greatest inductive subset of those ranges, asked of Z3
            clause by clause), add each such range as a premise of every body
            atom, and conjoin the ranges to the solution found
            ([PCSatCommon.WordRanges]; equisatisfiable, sound for both
            answers).  It is what lets [z3.int_to_bv] hand a body word
            to Z3 as a bit-vector rather than split it with an unbounded
            quotient *)
    elim_ite : bool; [@default false]
    propagate_lb_ub : bool; [@default false]
    simplification_with_smt : bool; [@default false]
  }
  [@@deriving yojson]

  (** Where the clauses mentioning no unknown are swept (each asked valid,
      an invalid one refuting the problem) before the later stages. *)
  type unknown_free_clauses = {
    sweep_before_finite_instances : bool; [@default false]
        (** after predicate elimination and before the finite instantiation
            of quantified sorts, ask every clause that mentions no unknown for
            validity, each at 500 ms and all within 5 s
            ([PCSatCommon.UnknownFreeSweep]); a clause shown invalid refutes the
            problem, which is then handed on as the single constraint [false].
            The certificate is that bare leaf, which the checker reports as not
            re-derived.  Where the finite instantiation's nested solve runs, it
            can spend the whole run before the coordinator's own sweep
            ([unknown_free_clauses.sweep]) is reached *)
    sweep_before_elimination : bool; [@default false]
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
    sweep_fork_margin_ms : int option; [@default None]
        (** [Some m]: every sweep (the two above and the one before the
            post-elimination hook, which runs whenever there is such a hook
            and the caller may refute) asks each clause in a
            forked copy killed after its 500 ms budget plus [m] ms, and reads
            back only a refutation; when no copy can be forked (another domain
            running, or the memory budget) the clause is asked here as with
            [None].  [None]: each clause is asked in this process, except one
            of a shape [Z3interface.may_not_return] refuses (a quantifier
            binding a sequence), which is not asked at all and refutes
            nothing; with [Some m] such a clause is asked, in the copy.  Why: Z3's
            sequence theory has a loop that reads neither its timeout nor its
            resource limit, and a sweep question over sequences under
            quantifiers, asked here with a 500 ms budget, has stayed open for
            25 s while the process grew from 0.6 GB to the 6 GB memory cap,
            which ends the run; the same question answers in well under a
            second in the runs where it returns.  Not exact: a copy asks with
            no Z3 timer (the thread serving one does not exist in a forked
            process), so a refutation found between 500 ms and the kill is
            read where the in-process question would have timed out, and an
            in-process answer that overran its budget is not waited for.  A
            refutation from a copy carries no model, which the sweep does not
            read. *)
  }
  [@@deriving yojson]

  type t = {
    enable : bool; [@default true]
    verbose : bool; [@default false]
    universal_function_expansion : int option; [@default None]
        (** [Some ms]: after the finite instantiation, try refuting the whole
            problem from instances of its universally quantified Boolean
            functions ([refute_by_universal_instances]): each at the constant
            [true] array or at a hole [lambda k. k <> p] for one fresh point
            [p], in the patterns all constant, one hole, two holes and all
            holes, the instances asked of Z3 together in a forked copy given
            [ms] milliseconds.  [None]: not tried. *)
    elimination : elimination;
        [@default Common.Util.config_default elimination_of_yojson "{}"]
    condensation : condensation;
        [@default Common.Util.config_default condensation_of_yojson "{}"]
    finite_forall_sorts : finite_forall_sorts;
        [@default Common.Util.config_default finite_forall_sorts_of_yojson {|["Instantiate", {}]|}]
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
    refute_by_unfolding : refute_by_unfolding;
        [@default Common.Util.config_default refute_by_unfolding_of_yojson {|["Unfold", {}]|}]
        (** after predicate elimination and before the finite instantiation
            of quantified sorts (beside the sweep above), unfold every unknown
            that has a fact clause through its step clauses (a head and body
            atoms of that unknown only, such as a transitivity law) for
            [refute_by_unfolding.depth] levels, put the unfolding in place of
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
    argument_reduction : argument_reduction;
        [@default Common.Util.config_default argument_reduction_of_yojson "{}"]
    sharing : sharing; [@default Common.Util.config_default sharing_of_yojson "{}"]
    clauses : clauses; [@default Common.Util.config_default clauses_of_yojson "{}"]
    unknown_free_clauses : unknown_free_clauses;
        [@default Common.Util.config_default unknown_free_clauses_of_yojson "{}"]
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
             ( "elimination",
               `Assoc
                 [
                   ("resolution_threshold", `Int resolution_threshold);
                   ("bool_vars", `Int num_elim_bool_vars);
                 ] );
             ( "argument_reduction",
               `Assoc
                 [
                   ( "reduce",
                     `List
                       (if reduce_pvar_args then [ `String "Reduce"; `Assoc [] ]
                        else [ `String "No_arg_reduction" ]) );
                 ] );
             (* the single-constructor split stays off here, whatever its
                code default: the engines that convert a problem through this
                configuration (MuCyc, MuVal's muCLP-from-CHC route, MuStrat,
                OptPCSat's optimizer, RCaml's constraint generation) rely on
                preprocessing collapsing a predicate-free residual to a
                constant.  The split can leave a quantified residual instead
                (case splits over the exposed fields and a pointwise array
                comparison), which MuCyc has no procedure for and answers
                [unknown] on, where PCSat's zero-unknown stage decides it *)
             ( "clauses",
               `Assoc
                 [ ("split_single_cons", `List [ `String "No_single_cons_split" ]) ]
             );
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

(** The value each of the preprocessor's flat switches takes under a
    configuration.  A variant of [Config] folds a switch and the parameters
    read only under it into one choice; the passes read booleans and options,
    and these functions unfold the choice.  Contract: under every choice each
    function returns the value the code reads, and where the choice makes a
    parameter inert (its mechanism is off) it returns that parameter's
    default, which no reader looks at: its readers are reached only under the
    constructor that carries it. *)
module ConfigSwitch = struct
  open Config

  let pvar_elim_valid_memo (c : Config.t) =
    match c.elimination.questions.memo with
    | Memo _ -> true
    | No_memo -> false

  let pvar_elim_valid_memo_alpha (c : Config.t) =
    match c.elimination.questions.memo with
    | Memo r -> r.alpha
    | No_memo -> true

  let pvar_elim_valid_memo_reasks (c : Config.t) =
    match c.elimination.questions.memo with
    | Memo r -> r.reasks
    | No_memo -> 4

  let pvar_elim_valid_memo_reask_timeout (c : Config.t) =
    match c.elimination.questions.memo with
    | Memo r -> r.reask_timeout_ms
    | No_memo -> 500

  let pvar_elim_valid_memo_reask_max_disjuncts (c : Config.t) =
    match c.elimination.questions.memo with
    | Memo r -> r.reask_max_disjuncts
    | No_memo -> 64
  let finite_forall_sorts (c : Config.t) =
    match c.finite_forall_sorts with
    | Instantiate _ -> true
    | No_finite_instances -> false

  let finite_forall_sorts_by_name (c : Config.t) =
    match c.finite_forall_sorts with
    | Instantiate r -> r.by_name
    | No_finite_instances -> true

  let finite_forall_sorts_targeted_instance (c : Config.t) =
    match c.finite_forall_sorts with
    | Instantiate r -> r.targeted
    | No_finite_instances -> true

  let finite_forall_sorts_max_instance_size (c : Config.t) =
    match c.finite_forall_sorts with
    | Instantiate r -> r.max_instance_size
    | No_finite_instances -> None

  let finite_forall_sorts_query_timeout (c : Config.t) =
    match c.finite_forall_sorts with
    | Instantiate r -> r.query_timeout_ms
    | No_finite_instances -> 2000

  let finite_forall_sorts_fork_query (c : Config.t) =
    match c.finite_forall_sorts with
    | Instantiate r -> r.fork_query
    | No_finite_instances -> true

  let finite_forall_sorts_charge_construction (c : Config.t) =
    match c.finite_forall_sorts with
    | Instantiate r -> r.charge_construction
    | No_finite_instances -> false

  let finite_forall_sorts_parallel (c : Config.t) =
    match c.finite_forall_sorts with
    | Instantiate r -> r.parallel
    | No_finite_instances -> false

  let finite_forall_sorts_nested_solve (c : Config.t) =
    match c.finite_forall_sorts with
    | Instantiate r -> (
        match r.nested with Nested_solve _ -> true | No_nested_solve -> false)
    | No_finite_instances -> false

  let finite_forall_sorts_nested_solve_budget (c : Config.t) =
    match c.finite_forall_sorts with
    | Instantiate r -> (
        match r.nested with
        | Nested_solve r -> r.budget_ms
        | No_nested_solve -> Some 10000)
    | No_finite_instances -> Some 10000

  let finite_forall_sorts_nested_solve_strict_budget (c : Config.t) =
    match c.finite_forall_sorts with
    | Instantiate r -> (
        match r.nested with
        | Nested_solve r -> r.strict_budget
        | No_nested_solve -> true)
    | No_finite_instances -> true

  let finite_forall_sorts_nested_solve_stage_deadline (c : Config.t) =
    match c.finite_forall_sorts with
    | Instantiate r -> (
        match r.nested with
        | Nested_solve r -> r.stage_deadline
        | No_nested_solve -> false)
    | No_finite_instances -> false

  let finite_forall_sorts_nested_solve_budget_after_first_round (c : Config.t) =
    match c.finite_forall_sorts with
    | Instantiate r -> (
        match r.nested with
        | Nested_solve r -> r.after_first_round_ms
        | No_nested_solve -> Some 2000)
    | No_finite_instances -> Some 2000

  let finite_forall_sorts_nested_solve_fresh_context (c : Config.t) =
    match c.finite_forall_sorts with
    | Instantiate r -> (
        match r.nested with
        | Nested_solve r -> r.fresh_context
        | No_nested_solve -> true)
    | No_finite_instances -> true
end

(* What a caller of [preprocess] wants from it, stated as a value rather than
   inferred from which unknowns it protects (a solving caller protects some
   too, so a non-empty protected set is not the sign of either purpose).

   - [Decide keep]: the caller asks whether the clauses are satisfiable.  Every
     stage may run, including the ones that refute: a refutation replaces the
     problem by the single constraint [false], which removes every unknown and
     is the right answer to that question.  The unknowns in [keep] are never
     eliminated, because the caller reads their solutions.
   - [Eliminate_keeping keep]: the caller only simplifies the clauses and
     eliminates the auxiliary unknowns, then reads the unknowns in [keep] (and
     the definitions of the eliminated ones) back.  The clauses may be
     unsatisfiable as they stand -- a fragment whose kept unknowns are
     placeholders to be synthesised anew, such as a fact [FN(x)] for every [x]
     beside a goal [not FN(2)] -- so a stage that would replace them by [false]
     would leave nothing to read back.  The unknown-free sweeps and the
     unfolding refutation do not run.

   Which stage runs under which purpose: every stage runs under [Decide]; under
   [Eliminate_keeping] every stage runs except the unknown-free sweeps (before
   the elimination, before the post-elimination hook, before the finite
   instances), the unfolding refutation and the finite instantiation of the
   quantified sorts, which read [may_refute].  The finite instantiation is a
   refutation like the others, and an [Eliminate_keeping] caller does produce
   sort variables: the refinement type checker eliminates the auxiliary
   unknowns of a polymorphic OCaml function before generalising it, with the
   function's type variables still sort variables.  Run there, the stage asked
   the solver a satisfiability question nobody wanted the answer to, and on a
   comparison [x <= y] at a type variable -- an ordering with no theory to
   encode it in until the variable is instantiated -- the encoder's refusal
   escaped as an uncaught exception and stopped the run. *)
module Purpose = struct
  type t = Decide of Ident.tvar_set | Eliminate_keeping of Ident.tvar_set

  (* the purpose of a caller that names nothing: decide, keeping no unknown *)
  let decide = Decide Set.Poly.empty

  (* the unknowns the elimination must not remove, under either purpose *)
  let kept = function Decide keep | Eliminate_keeping keep -> keep

  (* whether a stage that can replace the problem by [false] may run *)
  let may_refute = function Decide _ -> true | Eliminate_keeping _ -> false
end

module type PreprocessorType = sig
  val solve :
    ?witness:WitnessConfig.t ->
    (* the unknowns kept: [solve] always decides, so this is the set of its
       [Purpose.Decide] *)
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
    (* what the caller wants and which unknowns it keeps (see [Purpose]);
       [Purpose.decide] when omitted *)
    ?purpose:Purpose.t ->
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
       [unknown_free_clauses.sweep_before_finite_instances] does), and a
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

(* the questions [argument_reduction.share_determined.memo_questions] answered from an earlier
   identical one, over the process; read by the tests *)
let share_memo_hits = Atomic.make 0

(* how many times the unfolding refutation was started as a raced copy
   ([refute_by_unfolding.parallel]); read by the tests *)
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
   and (with [argument_reduction.share_determined.syntactic_first]) how many candidates fell back
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

  (* why a candidate equality was not taken as an unseen-variable one: for
     each side that is a variable, the reason, and the premise that sees it *)
  let unseen_refused ~two_values ~premises (l, r) =
    let side t other =
      match
        ClauseCone.unseen_var_why ~two_values ~premises ~other t
          (Term.sort_of t)
      with
      | `Unseen -> "unseen"
      | `Not_a_variable -> "not-a-variable"
      | `Other -> "other-side"
      | `Sort -> "sort " ^ Term.str_of_sort (Term.sort_of t)
      | `Seen p ->
          let s = Formula.str_of p in
          sprintf "seen-by %s"
            (if String.length s > 600 then String.prefix s 600 ^ "..." else s)
    in
    Out_channel.eprintf "SHAREUNSEEN l=%s r=%s | %s | %s\n%!"
      (String.prefix (Term.str_of l) 60)
      (String.prefix (Term.str_of r) 60)
      (side l r) (side r l)

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

(* Check the whole proposed family before installing any enumeration. Quoted
   source symbols can spell the generated #fin names, and a group member may
   be occupied even when the environment stores only the group's root. *)
let finite_instance_names_fresh ~names dtenv =
  let occupied =
    Set.Poly.of_list
    @@ List.concat_map (Map.Poly.data dtenv) ~f:(fun dt ->
         LogicOld.Datatype.name_of dt
         :: List.map (LogicOld.Datatype.dts_of dt)
              ~f:LogicOld.Datatype.name_of_dt)
  in
  List.for_all names ~f:(fun name -> not (Set.mem occupied name))

(* Cooperative finite-environment ownership. No callback runs when another
   owner holds the bracket. Ordinary exits restore the pre-extension snapshots;
   only an explicitly successful emission may retain its installed environment.
   The finally is active before freshness checking, construction or installation. *)
let with_finite_instance_scope ?(reset_pool = false) ~names f =
  if not (LogicOld.try_enter_env_bracket ()) then None
  else
    let original_dtenv = LogicOld.get_dtenv () in
    let original_fenv = LogicOld.get_fenv () in
    let committed = ref false in
    Common.Timer.protect
      ~finally:(fun () ->
        Common.Timer.protect ~finally:LogicOld.leave_env_bracket (fun () ->
          if not !committed then (
            LogicOld.set_fenv original_fenv;
            LogicOld.set_dtenv original_dtenv);
          if reset_pool then Z3Smt.Z3interface.clear_instance_pool ()))
      (fun () ->
        if not (finite_instance_names_fresh ~names original_dtenv) then None
        else
          match f original_dtenv original_fenv with
          | `Restore result -> Some result
          | `Commit result -> committed := true; Some result)

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
(* Refuting a problem from instances of its universal Boolean functions.

   The problem's clauses are implicitly closed over every variable that is not
   an unknown, including the array-sorted variables that stand for a
   [declare-forall-fun] with arguments.  Each closed clause therefore implies
   each of its instances, and so does every solution: a solution of the
   problem satisfies the conjunction of any set of instances.  If that
   conjunction, with the unknowns read as uninterpreted relations (and each
   functional unknown as an uninterpreted function, which is exact for the
   kind), is unsatisfiable, the problem has no solution.  The point [p] of the
   holes is a free constant, read existentially by the solver; an [unsat]
   says that no [p] admits a solution of the instances, which is more than
   needed.  A solver's [unsat] over an uninterpreted sort holds in every
   carrier, and a solution must exist in every model, so it transfers too.

   The instances: each Bool-valued array variable at [T] (the constant [true]
   array) or [H] ([lambda k. k <> p], written [store T p false]); the patterns are every variable at
   [T], each one at [H], each pair at [H], and all at [H] -- the shapes the
   hand refutations of agreement problems use (one or two parties shown a
   predicate with a hole, against the others shown everything).

   Each clause is closed on its own, so its universal functions are its own
   variables and its pattern is chosen independently of the other clauses';
   the point [p] is one constant for all of them, which is what lets an atom
   [F(H, ..)] derived from one clause's instance meet the same atom in
   another's.

   Contract: returns [Ok k] (the number of instances) only when the forked
   solver answered [unsat] for the conjunction; [Error reason] when it
   answered anything else, ran out of [ms], when no clause has such a
   variable or one has more than eight, or when the problem has an unknown of
   a kind other than ordinary and functional. *)
let refute_by_universal_instances ~ms pcsp =
  let unknowns = Map.key_set @@ PCSP.Problem.senv_of pcsp in
  let other_kinds =
    List.exists (PCSP.Problem.non_ord_kinds_of pcsp) ~f:(fun (_, k) ->
        not (Kind.is_fn k))
  in
  if other_kinds then Error "an unknown of a kind other than ordinary or functional"
  else
    let points = Hashtbl.Poly.create () in
    let point_of si =
      Hashtbl.find_or_add points si ~default:(fun () ->
          Term.mk_var (Ident.mk_fresh_tvar ~prefix:(Some "#hole_point_") ()) si)
    in
    let instance_of holes (x, srt) =
      let si = T_array.index_sort_of srt in
      (* the hole [lambda k. k <> p] written as the store it equals, so that
         the query stays in the array fragment the solver is complete for
         (a lambda makes it answer "incomplete (theory array)") *)
      let top = T_array.mk_const_array si T_bool.SBool (T_bool.mk_true ()) in
      if List.mem holes x ~equal:Ident.tvar_equal then
        T_array.mk_store si T_bool.SBool top (point_of si) (T_bool.mk_false ())
      else top
    in
    (* each clause is closed on its own, so its universal functions are its
       own variables and its instances are chosen independently of the other
       clauses'; the hole's point is one constant for all of them *)
    let clause_instances phi =
      let free =
        Set.to_list
        @@ Set.filter (Formula.term_sort_env_of phi) ~f:(fun (x, _) ->
            not (Set.mem unknowns x))
      in
      let arrays =
        List.filter free ~f:(fun (_, srt) ->
            match srt with
            | T_array.SArray (_, T_bool.SBool) -> true
            | _ -> false)
      in
      let names = List.map arrays ~f:fst in
      let rest =
        List.filter free ~f:(fun (x, _) ->
            not (List.mem names x ~equal:Ident.tvar_equal))
      in
      let patterns =
        List.dedup_and_sort ~compare:Stdlib.compare
        @@ ([] :: names :: List.map names ~f:List.return)
        @ List.concat_mapi names ~f:(fun i x ->
            List.filter_mapi names ~f:(fun j y ->
                if j > i then Some [ x; y ] else None))
      in
      ( List.length arrays,
        List.map patterns ~f:(fun holes ->
            let sub =
              Map.Poly.of_alist_exn
              @@ List.map arrays ~f:(fun ((x, _) as b) -> (x, instance_of holes b))
            in
            Formula.mk_forall rest @@ Formula.subst sub phi) )
    in
    let per_clause =
      List.map ~f:clause_instances @@ Set.to_list
      @@ PCSP.Problem.old_formulas_of pcsp
    in
    let widest = List.fold per_clause ~init:0 ~f:(fun m (n, _) -> max m n) in
    if widest = 0 || widest > 8 then
      Error
        (sprintf
           "a clause with %d Boolean universal functions (1 to 8 are tried)"
           widest)
    else
      let fn_funs =
        Map.Poly.map (PCSP.Problem.fnpvs_senv_of pcsp) ~f:(fun so ->
            let sorts =
              List.map ~f:Logic.ExtTerm.to_old_sort @@ Logic.Sort.args_of so
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
      let instances = List.concat_map per_clause ~f:snd in
      let phi = defunctionalise @@ Formula.and_of instances in
      let id = PCSP.Problem.id_of pcsp in
      let fenv = LogicOld.get_fenv () in
      match
        PCSatCommon.ForkedQuery.run ~ms (fun () ->
            match Z3Smt.Z3interface.check_sat ~id ~timeout:None fenv [ phi ] with
            | `Unsat -> "unsat"
            | `Sat _ -> "sat"
            | `Unknown r -> "unknown (" ^ r ^ ")"
            | _ -> "timeout")
      with
      | Some "unsat" -> Ok (List.length instances)
      | Some answer -> Error ("the solver answered " ^ answer)
      | None -> Error "no answer within the budget"

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
    ~fenv_substituted:(_ : LogicOld.FunEnv.t) pcsp =
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
        (* The problem's OWN functions, substituted -- not [fenv_substituted],
           the process-global environment, which also holds every definition
           the input declared and preprocessing has since stopped applying
           (a recursive function whose applications were replaced by graph
           unknowns, an unreached definition).  The instance is the problem
           with the sorts substituted, so it carries the substituted copy of
           the problem's own environment, as it does of every other part; the
           global one would add functions the original problem does not
           offer, and a consumer that
           enumerates the problem's functions treats them as vocabulary: the
           hypothesis space applies each one to every combination of terms of
           its argument sorts, filling a sort it has no term of with a dummy
           constant.  On a Thrust input with 23 such definitions over
           sixteen quantified sorts that took one unknown's term set from 131
           terms (the original problem's) to 969,244, and the nested solve
           spent minutes and gigabytes building templates over them.  Each
           entry equals the one [fenv_substituted] holds where the problem's
           definition is the global one.  [fenv_substituted] is what the
           caller installs globally for conversion, and is not read here. *)
        PCSP.Params.fenv =
          snd (finite_instance_envs smap Map.Poly.empty params.PCSP.Params.fenv);
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

  let of_problem_here pcsp =
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

  (* [of_problem pcsp]: [of_problem_here pcsp] computed in a forked copy of
     this process ([PCSatCommon.ForkedQuery.run], 60 s), so that computing it
     changes nothing this process reads afterwards.  It is computed only while
     a raced copy is alive, and printing the problem goes through the
     simplifier and the conversion to the old term language, which draw fresh
     names and may ask the solver: computed here, it made the process ask its
     later questions in another state, so whether a refutation was found
     depended on whether a raced copy happened to be alive at the checkpoint
     (measured: an unfolding refutation found in 10 s in 3 of 3 runs without
     the copy, in 0 of 3 with it, the guessed sequence lengths of its
     relaxation differing).  Contract: the process's state after the call is
     the state before it; the result is [of_problem_here pcsp] when the copy
     answers, and otherwise a string of this process alone, which no other
     process's digest equals, so a failed copy can only keep a duplicate race
     running, never drop a race that is not one. *)
  let of_problem pcsp =
    match
      PCSatCommon.ForkedQuery.run ~ms:60000 (fun () -> of_problem_here pcsp)
    with
    | Some d -> d
    | None ->
        sprintf "race digest unavailable in process %d"
          (Pid.to_int (Core_unix.getpid ()))
end

(* the nesting depth of [solve] in this domain: a nested solve (a finite
   instance's, say) is not the problem a raced copy is compared on.  Per
   domain, since MuVal solves its primal and dual side at once in two domains
   and one side's nesting is not the other's; a spawned domain starts from its
   parent's depth *)
let solve_depth_key =
  Domain.DLS.new_key ~split_from_parent:(fun r -> ref !r) (fun () -> ref 0)

let solve_depth () = Domain.DLS.get solve_depth_key

(* set by the solver while its upper-bound definition probe solves the input
   with some unknowns defined, read by [Split_single_cons
   {outside_upper_bound_probe = true}]; per domain, as [solve_depth], and a
   spawned domain or a forked copy starts from its parent's value *)
let in_upper_bound_probe_key =
  Domain.DLS.new_key ~split_from_parent:(fun r -> ref !r) (fun () -> ref false)

let in_upper_bound_probe () = Domain.DLS.get in_upper_bound_probe_key

(* set while [solve] preprocesses its input a second time for the early
   relation pin, read by [Split_single_cons {outside_early_pins = true}],
   which then leaves that problem unsplit; per domain, as
   [in_upper_bound_probe] *)
let in_early_pins_copy_key =
  Domain.DLS.new_key ~split_from_parent:(fun r -> ref !r) (fun () -> ref false)

let in_early_pins_copy () = Domain.DLS.get in_early_pins_copy_key

(* set by the single-constructor split when it split at least one clause
   variable; [solve] clears it before its preprocessing, reads it after and
   restores the value it found, so a nested solve's split is not taken for the
   enclosing one's.  Per domain, as [in_upper_bound_probe] *)
let single_cons_split_acted_key =
  Domain.DLS.new_key ~split_from_parent:(fun r -> ref !r) (fun () -> ref false)

let single_cons_split_acted () = Domain.DLS.get single_cons_split_acted_key

(* set by a caller that reads only a [sat] of the problem it solves (a probe
   whose [unsat] is discarded) for the length of that solve: [preprocess] then
   runs none of the costly stages that can only refute -- the refutation by
   unfolding, the finite instantiation of the quantified sorts and the
   universal-function instances (the unknown-free sweeps still run).  Each
   of them returns its problem unchanged or the constraint [false], so skipping one changes no [sat] the caller can reach: a problem
   the stage would refute has no solution, and on any other the stage is the
   identity.  What changes is time, both ways: the stage's own time is saved
   (inside a probe's bounded solve such a stage is not raced in a forked copy
   but run in sequence, and on a Rust-derived input the refutation by
   unfolding alone took 51 s of a probe whose budget is 60 s, refuting
   nothing), and a problem the stage would have refuted early now runs on to
   the caller's budget.  Per domain, as [in_upper_bound_probe] *)
let refutation_unread_key =
  Domain.DLS.new_key ~split_from_parent:(fun r -> ref !r) (fun () -> ref false)

let refutation_unread () = Domain.DLS.get refutation_unread_key

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
      if String.equal v ("exit:" ^ label) then Common.ProcessExit.exit 0

(* An instrument: with COAR_PREPROC_DIGEST=FILE, one line per preprocessing
   stage boundary is appended to FILE -- the stage's name, the fresh-name
   counter, and the digest of the problem's print -- so that two
   preprocessings of one input in one process (the counter set to one value
   before each) can be compared stage by stage and the first stage whose
   output differs found.  It decides nothing, and unset it does nothing.
   Read at start-up, not through a [lazy]. *)
let stage_digest_env = Stdlib.Sys.getenv_opt "COAR_PREPROC_DIGEST"

let stage_digest label pcsp =
  match stage_digest_env with
  | None -> ()
  | Some file ->
      let line =
        sprintf "STAGE\t%s\t%d\t%s" label
          (Atomic.get Ident.tvar_count)
          (Stdlib.Digest.to_hex
             (Stdlib.Digest.string (PCSP.Problem.str_of pcsp)))
      in
      Out_channel.with_file file ~append:true ~f:(fun oc ->
          Out_channel.output_string oc line;
          Out_channel.newline oc);
      (* the same line in the solver interface's resource-counter log, when
         one is kept, so that its checks are segmented by stage *)
      Z3Smt.Z3interface.rlimit_log_line line

module Make (Config : Config.ConfigType) = struct
  let () =
    (* the subsumption's implementation and the resolution index are read by
       the eliminator only when it subsumes *)
    (match Config.config.elimination.subsume with
    | No_subsume -> ()
    | Subsume { impl; resolution_index } -> (
        if resolution_index then
          Atomic.set PvarEliminator.resolution_index true;
        match impl with
        | Plain -> ()
        | Hashed -> Atomic.set PvarEliminator.ClauseSubsume.hash_prefilter true
        | Interned -> Atomic.set PvarEliminator.ClauseSubsume.interned true
        | Persistent -> Atomic.set PvarEliminator.ClauseSubsume.persistent true));
    if Config.config.elimination.speed.cnf_shared_fvs then
      Atomic.set PvarEliminator.cnf_shared_fvs true;
    if Config.config.elimination.speed.resolution_atom_pvs_memo then
      Atomic.set PvarEliminator.resolution_atom_pvs_memo true;
    if Config.config.elimination.widest_first then
      Atomic.set PvarEliminator.widest_first true;
    if Config.config.elimination.questions.words.first then
      Atomic.set PvarEliminator.words_first true;
    Option.iter Config.config.elimination.questions.axioms_first_ms ~f:(fun ms ->
        Atomic.set PvarEliminator.seq_axioms_first_ms (Some ms));
    if Config.config.elimination.questions.words.keep_proved then
      Atomic.set PvarEliminator.words_keep_proved true;
    if Config.config.elimination.questions.words.skip_spent_searches then
      PCSatCommon.SeqInstantiation.skip_spent_budget_searches := true;
    (match Config.config.elimination.questions.defer_pure with
    | Ask_in_round -> ()
    | Defer_to_round_end -> Atomic.set PvarEliminator.defer_pure_to_round_end true
    | Defer_to_verdict -> Atomic.set PvarEliminator.defer_pure_to_verdict true);
    Option.iter Config.config.elimination.questions.words.full_major_every ~f:(fun n ->
        Atomic.set PvarEliminator.words_full_major_every (Some n));
    if Config.config.elimination.questions.rewrites.implied_factor_equalities then
      Atomic.set PvarEliminator.implied_factor_equalities true;
    Option.iter Config.config.elimination.questions.kill_factor ~f:(fun k ->
        Atomic.set PvarEliminator.valid_kill_factor (Some k));
    Option.iter Config.config.elimination.questions.reask_rlimit ~f:(fun r ->
        Atomic.set PvarEliminator.valid_reask_rlimit (Some r));
    if Config.config.elimination.questions.rewrites.onepoint then
      Atomic.set PvarEliminator.onepoint_questions true;
    Option.iter Config.config.elimination.questions.cvc5.rlimit ~f:(fun r ->
        Atomic.set PvarEliminator.cvc5_rlimit (Some r));
    Option.iter Config.config.elimination.questions.pieces_first
      ~f:(fun { z3_ms; cvc5_ms } ->
        Atomic.set PvarEliminator.pieces_first (Some (z3_ms, cvc5_ms)));
    Option.iter Config.config.elimination.questions.fork.quantified_margin_ms ~f:(fun m ->
        Atomic.set PvarEliminator.fork_quantified_margin_ms (Some m));
    Atomic.set PvarEliminator.fork_seq_unreturning
      Config.config.elimination.questions.fork.seq_unreturning;
    (match Config.config.elimination.complete with
    | Complete_elimination { invalid_first_ms = Some ms; _ } ->
        Atomic.set PvarEliminator.invalid_first_ms (Some ms)
    | _ -> ());
    if Config.config.elimination.questions.rewrites.split_int_binders_at_ite then (
      Atomic.set PvarEliminator.split_int_binders_at_ite true;
      (* with [verbose], one stderr line at exit tallying the questions
         rewritten: a diagnostic, so a plain run's output stays the answer *)
      if Config.config.verbose then IntBinderSplit.report_tallies ());
    if Config.config.elimination.speed.cnf_clause_tree then
      Atomic.set PvarEliminator.cnf_clause_tree true;
    if Config.config.elimination.speed.reuse_unassigned_cnf then
      Atomic.set PvarEliminator.reuse_unassigned_cnf true;
    if Config.config.sharing.clause_dt_conversion then
      Atomic.set Clause.shared_dt_conversion true;
    (match Config.config.sharing.formulas with
    | No_sharing -> ()
    | Term_conversions -> Atomic.set Logic.ExtTerm.share_term_conversion true
    | Rebuilt_formulas ->
        Atomic.set Logic.ExtTerm.share_term_conversion true;
        Atomic.set Logic.ExtTerm.share_term_conversion_terms true;
        Atomic.set Evaluator.share_simplify true;
        Atomic.set Normalizer.share_normalize true;
        Atomic.set PCSP.Problem.share_unused_params_fvs true);
    if Config.config.elimination.speed.triv_fn_linear then
      Atomic.set PCSP.Problem.triv_fn_linear true;
    if Config.config.sharing.let_passes then
      Atomic.set LogicOld.share_let_passes true;
    if Option.is_some Config.config.elimination.max_growth then
      Atomic.set PvarEliminator.resolution_max_growth
        Config.config.elimination.max_growth;
    (* [elimination.set_aside] is not set process-wide: [elim_pvs] receives
       this instance's value ([set_aside] below), so that MuVal's primal and
       dual, each built from its own configuration, can differ in it *)
    ()

  let config = Config.config
  let m = Debug.Config.(if config.verbose then enable else disable)

  module Debug = Debug.Make ((val m))

  (* the library module's helpers, before the functor application below
     shadows its name *)
  module UnknownFreeCondenseLib = PvarEliminator.UnknownFreeCondense

  type set_aside = PvarEliminator.set_aside = {
    aside_max_clauses : int option;
    aside_definitional : bool;
    aside_shared_args : bool;
    aside_gaining : bool;
    aside_trigger : int option;
  }

  module PvarEliminator =
    PvarEliminator.Make
      ((val m))
      (struct
        let resolution_threshold = config.elimination.resolution_threshold

        (* the eliminator reads the complete elimination as four values, a
           bound of 0 standing for none *)
        let ( resolution_complete_max_clauses,
              resolution_complete_prebound,
              resolution_complete_early_exit,
              resolution_complete_budget_ms,
              resolution_complete_skip_recursive ) =
          match config.elimination.complete with
          | No_complete_elimination -> (0, false, false, None, false)
          | Complete_elimination
              {
                max_clauses;
                prebound;
                early_exit;
                budget_ms;
                invalid_first_ms = _;
                skip_recursive;
              } ->
              (max_clauses, prebound, early_exit, budget_ms, skip_recursive)
        let propagate_lb_ub = config.clauses.propagate_lb_ub
        let condense_resolvents = config.condensation.resolvents
        let condense_pure_resolvents = config.condensation.pure.resolvents
        let condense_pure_min_side_size = config.condensation.pure.min_side_size

        let condense_pure_unknown_free_resolvents =
          config.condensation.pure.unknown_free_resolvents

        let condense_pure_max_checks = config.condensation.pure.max_checks

        let condense_pure_shape_candidates =
          config.condensation.pure.shape.candidates

        let condense_pure_shape_commutative =
          config.condensation.pure.shape.commutative

        let condense_pure_inclusion_candidates =
          config.condensation.pure.inclusion

        let condense_pure_max_search_nodes = config.condensation.pure.max_search_nodes
        let condense_pure_memo_failures = config.condensation.pure.memo_failures

        (* only ever turned on: the switch is process-wide *)
        let () =
          if config.elimination.dedup_alpha_disjuncts then
            PvarEliminator.AlphaDedup.enabled := true

        let () =
          if config.condensation.pure.joint.condense then PvarEliminator.joint_condense := true;
          if config.elimination.drop_derived_premises then
            PvarEliminator.drop_derived_premises := true;
          if config.condensation.pure.joint.prune_doomed then
            PvarEliminator.joint_prune_doomed := true

        let () =
          if config.condensation.unknown_free_resolvents then
            PvarEliminator.condense_unknown_free_resolvents := true

        let () =
          Atomic.set ClauseOld.condense_cbag_memo config.condensation.pure.cbag_memo;
          Atomic.set ClauseOld.condense_pattern_memo
            config.condensation.pure.pattern_memo;
          PvarEliminator.merge_pattern_prune :=
            config.condensation.pure.merge_pattern.prune;
          PvarEliminator.merge_pattern_gate :=
            config.condensation.pure.merge_pattern.gate
        let split_seq_reads = config.elimination.questions.rewrites.split_seq_reads
        let valid_timeout = config.elimination.questions.timeout_ms
        let valid_rlimit = config.elimination.questions.rlimit
        let seq_axiom_rlimit = config.elimination.questions.seq_axiom_fallback.rlimit
        let valid_fresh_quantified = config.elimination.questions.fresh_quantified
        let valid_memo = ConfigSwitch.pvar_elim_valid_memo config

        let valid_memo_reasks = ConfigSwitch.pvar_elim_valid_memo_reasks config

        let valid_memo_reask_timeout =
          ConfigSwitch.pvar_elim_valid_memo_reask_timeout config

        let valid_memo_reask_max_disjuncts =
          ConfigSwitch.pvar_elim_valid_memo_reask_max_disjuncts config

        let valid_warm_reask_ms = config.elimination.questions.warm_reask_ms

        let valid_memo_alpha = ConfigSwitch.pvar_elim_valid_memo_alpha config

        let valid_defer_pure_min_disjuncts =
          config.elimination.questions.defer_pure_min_disjuncts

        let seq_axiom_fallback_ms = config.elimination.questions.seq_axiom_fallback.cap_ms
        let seq_axiom_fallback_once = config.elimination.questions.seq_axiom_fallback.once

        let seq_axiom_fallback_after_refusal_only =
          config.elimination.questions.seq_axiom_fallback.after_refusal_only

        let seq_axiom_fallback_charge_build =
          config.elimination.questions.seq_axiom_fallback.charge_build

        let split_seq_prefix_over_concat =
          config.elimination.questions.rewrites.split_seq_prefix_over_concat

        let guarded_length_only_sequences =
          config.elimination.questions.rewrites.guarded_length_only_sequences

        let fork_refused_ms = config.elimination.questions.fork.refused_ms
        let cvc5_retry_ms = config.elimination.questions.cvc5.retry_ms
        let subsume_clauses =
          match config.elimination.subsume with
          | No_subsume -> false
          | Subsume _ -> true
        let tautology_test = config.elimination.tautology_test
        let assign_before_cnf = config.elimination.assign_before_cnf
        let merge_definitions = config.elimination.merge_definitions
      end)

  module DimReducer = DimReducer.Make ((val m))

  (* [simplify_clauses ~id ~fenv ~timeout exi_senv items]: each formula of
     [items] converted to the old representation, normalised, simplified (and,
     with [simplification_with_smt], simplified by Z3), converted back, and
     then freed of its universally quantified variables that only one-point
     rules bind ([Qelim.elim_free_univ_vars]), the images in the positions of
     their formulas.

     The steps run one at a time over all the formulas (stage by stage), each
     step that reads a memo in its own scope of it over every formula, so a
     subformula the formulas share is rebuilt once and stays shared: the
     normaliser's and the simplifier's memos for the normalisation, the
     simplification and the elimination (which simplifies too), and, under
     [share_term_conversion_terms], the term-conversion tables for the
     conversion to the old representation, the conversion back and the
     elimination (which converts both ways); the two directions keep separate
     tables, so a scope around both shared nothing between them.  Why stage
     by stage and not formula by formula under one scope: a memo keeps every
     node it was asked about and its image until its scope ends, so one scope
     around the whole pipeline held every intermediate formula of every step
     for every formula until the last one was done.  The values are those of
     the pipeline run formula by formula (each step is a function of its
     formula and of environments no step changes, and a memo hit stands for a
     recomputation to an equal value); fresh names are drawn in a different
     order only when more than one step draws, and then the results differ only
     in the names of bound variables. *)
  let simplify_clauses ~id ~fenv ?(timeout = Some 20000) exi_senv items =
    let simp =
      if config.clauses.simplification_with_smt then
        Z3Smt.Z3interface.simplify ~id fenv ~timeout
      else Fn.id
    in
    let ph = Common.PhaseTime.with_phase in
    let shared f =
      Normalizer.with_shared_normalize @@ fun () ->
      Evaluator.with_shared_simplify f
    in
    let converting f =
      if Atomic.get Logic.ExtTerm.share_term_conversion_terms then
        Logic.ExtTerm.with_shared_term_conversion f
      else f ()
    in
    (* left to right, as formula by formula *)
    let in_order g l =
      List.rev @@ List.fold l ~init:[] ~f:(fun acc x -> g x :: acc)
    in
    let items =
      converting @@ fun () ->
      shared @@ fun () ->
      in_order
        (fun (uni_senv, phi) ->
          ( uni_senv,
            ph "to-old" (fun () ->
                Logic.ExtTerm.to_old_fml exi_senv uni_senv phi)
            |> fun phi ->
            ph "normalize" (fun () -> Normalizer.normalize phi) ))
        items
    in
    let items =
      shared @@ fun () ->
      in_order
        (fun (uni_senv, phi) ->
          (uni_senv, ph "eval-simplify" (fun () -> Evaluator.simplify phi)))
        items
    in
    let items =
      converting @@ fun () ->
      in_order
        (fun (uni_senv, phi) ->
          let phi =
            try simp phi with exn_ when not (Common.Timer.is_async exn_) -> phi
          in
          (uni_senv, ph "of-old" (fun () -> Logic.ExtTerm.of_old_formula phi)))
        items
    in
    converting @@ fun () ->
    shared @@ fun () ->
    in_order
      (fun (uni_senv, phi) ->
        let uni_senv, _, phi =
          ph "free-univ" (fun () ->
              Qelim.elim_free_univ_vars Map.Poly.empty exi_senv
                (uni_senv, [], phi))
        in
        (uni_senv, phi))
      items

  let simplify ?(timeout = Some 20000) pcsp =
    let id = PCSP.Problem.id_of pcsp in
    let fenv = PCSP.Problem.fenv_of pcsp in
    if PCSP.Problem.is_cnf pcsp then pcsp
    else
      (* with [sharing.formulas = Rebuilt_formulas], the memo and conversion
         scopes of [simplify_clauses], each over every clause, so the
         subformulas the clauses share are simplified once and stay shared
         (the same results) *)
      PCSP.Problem.map_if_raw pcsp ~f:(fun phis ->
          (* the images added in the order [Set.Poly.map] adds them, so the
             set has the tree shape it had *)
          List.fold ~init:Set.Poly.empty ~f:Set.add
          @@ simplify_clauses ~id ~fenv ~timeout (PCSP.Problem.senv_of pcsp)
          @@ Set.to_list phis)

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
      if 0 < num_bool_vars && num_bool_vars <= config.elimination.bool_vars then
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
    if config.elimination.bool_vars <= 0 || PCSP.Problem.is_cnf pcsp then pcsp
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
     [((Leq 0 t) u)] as a definition (LinearArbitrary_kept/01.c.small, found by
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
     unknowns.  See [elimination.drop_implied_body_atoms] in the configuration for why
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
                  (* Only this clause's universally quantified variables
                     may be instantiated; a free known function head is a
                     fixed background symbol, even if no other atom uses it. *)
                  Map.Poly.mem senv x
                  && (not (Set.mem others x)) && not (Map.Poly.mem exi_senv x))
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

  (* Rewrite every clause that applies no unknown by cancellation of
     sequence equations, renaming by variable equations, and condensation of
     its disjuncts, each quantified disjunct's bound variables first renamed
     canonically ([condense_final_unknown_free_clauses]).
     Contract: each returned clause is equivalent to its input in every model
     (cancellation is exact in the free monoid of sequences; a disjunct
     [x != y] between variables of one sort is the renaming [y := x] of the
     universal closure; canonical bound names are an alpha-renaming of one
     disjunct; condensation drops only disjuncts that a renaming of
     variables occurring nowhere else maps onto disjuncts that stay), and a
     clause on which nothing changes is returned as it is.  A clause that
     applies an unknown, one with no equation between two non-integer
     variables once cancelled, and a problem not in clausal form, are left
     alone. *)
  let condense_final_unknown_free_clauses pcsp =
    match PCSP.Problem.clauses_of_opt ~full_clauses:false pcsp with
    | None -> pcsp
    | Some cls ->
        let exi_senv = PCSP.Problem.senv_of pcsp in
        let unknowns = Map.key_set exi_senv in
        PCSP.Problem.of_clauses ~params:(PCSP.Problem.params_of pcsp)
        @@ Set.Poly.map cls ~f:(fun cl ->
            let senv, ps, ns, phi =
              Common.PhaseTime.with_phase "to-old" (fun () ->
                  Clause.to_old_clause exi_senv cl)
            in
            if not (Set.is_empty ps && Set.is_empty ns) then cl
            else
              let phi' = UnknownFreeCondenseLib.disjuncts ~unknowns phi in
              if Stdlib.(phi' == phi) then cl
              else (
                (* counted only: a clause this pass rewrote *)
                Common.PhaseTime.event_here "condensed";
                Debug.print
                @@ lazy
                     (sprintf
                        "unknown-free clause condensed: %d disjuncts (size %d) \
                         -> %d (size %d)"
                        (List.length (Formula.disjuncts_list_of phi))
                        (Formula.ast_size phi)
                        (List.length (Formula.disjuncts_list_of phi'))
                        (Formula.ast_size phi'));
                Common.PhaseTime.with_phase "of-old" @@ fun () ->
                let cl' = Clause.of_old_clause (senv, ps, ns, phi') in
                let fvs = Clause.fvs_of cl' in
                let senv', ps', ns', phi' = cl' in
                Clause.canon
                  (Map.Poly.filter_keys senv' ~f:(Set.mem fvs), ps', ns', phi')))

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
     question undecided the two can keep different sets (a proof the
     one-by-one question did not reach; an undecided answer remembered rather
     than asked again), each kept candidate proved.  [slice_questions] first asks the conjunction on the premises
     connected to the candidates' variables ([ClauseCone.slice]), whose proof
     proves the whole question.

     [unseen_vacuity] answers every candidate with a side the premises
     cannot see ([ClauseCone.unseen_var]) by one question per clause and
     round, whether the premises are unsatisfiable: such a candidate's own
     question is equivalent to that one, and a conjunction containing it is
     too, so the other candidates of the atom are asked as without the
     switch when the premises are not proved unsatisfiable, and all are kept
     when they are. *)
  (* numbers the questions [COAR_SHARE_VALID_DUMP] keeps, over the process *)
  let share_dump_count = Atomic.make 0

  let rec share_determined_pvar_args ?(budget_ms = None) ?(fallback_cap = None)
      ?(syntactic_first = false) ?(slice_questions = false)
      ?(memo_questions = false) ?(memo_undecided = false)
      ?(unseen_vacuity = false) ?(collections_only = false) ~bpvs ~timeout pcsp
      =
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
        ~slice_questions ~memo_questions ~memo_undecided ~unseen_vacuity
        ~collections_only ~bpvs pcsp
    with
    | r -> r
    | exception Share_budget_spent ->
        Debug.print
        @@ lazy
             "[share_determined_pvar_args] budget spent: problem returned \
              unchanged";
        unchanged

  and share_determined_pvar_args_body ~question_timeout ~syntactic_first
      ~slice_questions ~memo_questions ~memo_undecided ~unseen_vacuity
      ~collections_only ~bpvs pcsp =
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
                  (* [collections_only]: the unknown is kept only when some
                     candidate pairs a sequence- or array-sorted leaf with a
                     part of its sort in another argument; decided from the
                     signature, before any question *)
                  let collection_pair () =
                    List.existsi ps ~f:(fun i pi ->
                        List.exists pi ~f:(fun (_, ls, leaf) ->
                            leaf
                            && (match ls with
                               | T_seq.SSeq _ | T_array.SArray _ -> true
                               | _ -> false)
                            && List.existsi ps ~f:(fun j pj ->
                                   i <> j
                                   && List.exists pj ~f:(fun (_, rs, _) ->
                                          String.equal (Term.str_of_sort ls)
                                            (Term.str_of_sort rs)))))
                  in
                  if List.is_empty cands then None
                  else if collections_only && not (collection_pair ()) then
                    None
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
             by the time limit and the simplified question.  A valid or
             invalid answer is a fact about the formula, so a second asking
             that decides gives the same answer; an undecided answer is not
             reused unless [memo_undecided], since the same question asked
             again in a context that has already worked on it can be decided
             where the first asking was not *)
          let memo = Hashtbl.PolyDeep.create () in
          let rec ask ?(kind = "whole") phi =
            (* raises [Share_budget_spent] when the budget is gone, before any
               work on the question; never from inside the solver call *)
            let timeout = question_timeout () in
            let phi = Evaluator.simplify phi in
            if not memo_questions then ask_simplified ~kind ~timeout phi
            else
              (* an undecided answer is kept too, but reused only with
                 [memo_undecided]; otherwise the question is asked again, and
                 the events count how often that happens and how often the
                 second asking decides *)
              let asked () =
                let v = ask_simplified ~kind ~timeout phi in
                Hashtbl.set memo ~key:(timeout, phi) ~data:v;
                v
              in
              match Hashtbl.find memo (timeout, phi) with
              | Some `Undecided when memo_undecided ->
                  Common.PhaseTime.event "share-undecided-reused";
                  `Undecided
              | Some `Undecided -> (
                  Common.PhaseTime.event "share-undecided-repeat";
                  match asked () with
                  | `Undecided -> `Undecided
                  | v ->
                      Common.PhaseTime.event "share-undecided-repeat-decided";
                      v)
              | Some v ->
                  Atomic.incr share_memo_hits;
                  v
              | None -> asked ()
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
          (* [unseen_vacuity]: per (clause, body key), whether the clause's
             premises with the hypotheses are proved unsatisfiable *)
          let vacuity = Hashtbl.Poly.create () in
          (* [unseen_vacuity]: whether premises about one variable alone admit
             two different values of it, asked of Z3 once per premise list
             (only a satisfiable answer is read) *)
          let two_values_memo = Hashtbl.Poly.create () in
          let two_values ps v srt =
            let key = String.concat_map_list ~sep:"\n" ps ~f:Formula.str_of in
            Hashtbl.find_or_add two_values_memo key ~default:(fun () ->
                let t0 = if census then Common.Clock.now_s () else 0. in
                let r =
                  match ClauseCone.two_value_query ~premises:ps v srt with
                  | None -> false
                  | Some query -> (
                      match
                        Z3Smt.Z3interface.check_sat ~timeout:(Some 1000) ~id fenv query
                      with
                      | `Sat _ -> true
                      | _ -> false
                      | exception exn_ when not (Common.Timer.is_async exn_) ->
                          false)
                in
                if census then
                  Census.timed "two-values" ~valid:r
                    (Common.Clock.now_s () -. t0);
                r)
          in
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
                  (* [premises => false]: the question every candidate with a
                     side the premises cannot see is equivalent to *)
                  let vacuous =
                    lazy
                      (match Hashtbl.find vacuity (k, body_key) with
                      | Some b -> b
                      | None ->
                          let b =
                            valid ~kind:"vacuity"
                              (Formula.mk_imply hyp (Formula.mk_false ()))
                          in
                          Hashtbl.set vacuity ~key:(k, body_key) ~data:b;
                          b)
                  in
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
                              (* the candidates with a side the premises
                                 cannot see, and the others: each of the
                                 first holds exactly when the premises are
                                 unsatisfiable ([ClauseCone.unseen_var]) *)
                              let unseen_of cs =
                                if not unseen_vacuity then ([], cs)
                                else
                                  List.partition_tf cs ~f:(fun c ->
                                      let ok =
                                        ClauseCone.unseen_side ~two_values
                                          ~premises:(Lazy.force premises)
                                          (sides args c)
                                      in
                                      if census && not ok then
                                        Census.unseen_refused ~two_values
                                          ~premises:(Lazy.force premises)
                                          (sides args c);
                                      ok)
                              in
                              if not syntactic_first then
                                let unseen, seen = unseen_of cs in
                                if
                                  (not (List.is_empty unseen))
                                  && Lazy.force vacuous
                                then live
                                else
                                  (* with an unseen candidate present, the
                                     conjunction of all of them is the
                                     vacuity question just answered no, so
                                     only the others are asked *)
                                  let seen' =
                                    if List.is_empty seen then []
                                    else if
                                      valid ~kind:"whole-conj"
                                        (Formula.mk_imply hyp (goal_of seen))
                                    then seen
                                    else List.filter seen ~f:whole
                                  in
                                  let cs' =
                                    List.filter cs ~f:(fun c ->
                                        List.mem seen' c ~equal:phys_equal)
                                  in
                                  Map.Poly.set live ~key:p ~data:(sorts, cs')
                              else
                                let residual =
                                  List.filter_map synl ~f:(fun (c, b) ->
                                      if b then None else Some c)
                                in
                                let unseen, residual_seen = unseen_of residual in
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
                                  if
                                    (not (List.is_empty unseen))
                                    && Lazy.force vacuous
                                  then residual
                                  else
                                    let residual = residual_seen in
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

  let preprocess ?(witness = WitnessConfig.default) ?(purpose = Purpose.decide)
      ?(oracle = None) ?(normalize_params = false)
      ?(solver : (PCSP.Problem.t -> State.output Or_error.t) option = None)
      ?(finite_certificate = ref None) ?finite_race ?post_elim:post_elim_opt pcsp =
    (* the closure below would otherwise capture [pcsp] and keep the
       unnormalised problem reachable until preprocessing returns, although
       every step after [normalize] reads only its normal form (the binding is
       shadowed there): on a large input that is a second copy of the clause
       set held to the end. The body takes the problem out of the cell once,
       so the original is collectable as soon as [normalize] has returned *)
    let pcsp =
      if Config.config.sharing.share_input then
        Common.PhaseTime.with_phase "dag-share" @@ fun () ->
        PCSP.Problem.map_if_raw ~f:Common.DagShare.share pcsp
      else pcsp
    in
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
      Set.union (Purpose.kept purpose)
        (PCSP.Parser.premise_unknowns_of (PCSP.Problem.senv_of pcsp))
    in
    let stage, _ = Common.PhaseTime.stages () in
    let stage name pcsp =
      (* a stage boundary is a safe point to end a probe whose strict deadline
         has passed ([SolveDeadline.check_at_stage]) *)
      PCSatCommon.SolveDeadline.check_at_stage ();
      share_census ("before " ^ name) pcsp;
      stage_digest name pcsp;
      stage name
    in
    let orig_senv = PCSP.Problem.senv_of pcsp in
    Debug.print @@ lazy "**************** preprocessing  ****************";
    Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
    Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
    Debug.print @@ lazy "************************************************";
    let () = stage "normalize" pcsp in
    let pcsp =
      Common.PhaseTime.with_phase "problem-normalize" (fun () ->
          PCSP.Problem.normalize pcsp)
    in
    share_census "after normalize" pcsp;
    Debug.print @@ lazy "normalized:";
    Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
    if print_pcsp then (
      Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
      Debug.print @@ lazy "");
    (* a single-valued predicate is solved as a domain predicate and a
       functional one; no-op without [Uniq] kinds *)
    let pcsp = PCSP.Problem.decompose_uniq pcsp in
    let pcsp =
      Common.PhaseTime.with_phase "nnf" (fun () -> PCSP.Problem.to_nnf pcsp)
    in
    let pcsp =
      if config.clauses.encode_head_disjunctions then
        PCSP.Problem.encode_head_disjunctions pcsp
      else pcsp
    in
    let pcsp =
      if config.clauses.instantiate_quantified_premises then
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
      (* guards the tester normal form rewrote in this problem; the tidying
         after the elimination of the unknowns runs only when it is positive *)
      let tester_guards = ref 0 in
      let pcsp =
        if config.clauses.tester_normal_form && not (PCSP.Problem.is_cnf pcsp)
        then (
          let () = stage "tester-normal-form" pcsp in
          let count = tester_guards in
          let pcsp =
            Common.PhaseTime.with_phase "tester-normal-form" (fun () ->
                PCSP.Problem.map_old_changed pcsp ~f:(fun (uni_senv, phi) ->
                    let uni_senv, phi, n =
                      Evaluator.tester_normal_form_free_vars uni_senv phi
                    in
                    count := !count + n;
                    if n = 0 then None else Some (uni_senv, phi)))
          in
          Debug.print
          @@ lazy
               (sprintf "tester-guarded selector reads rewritten: %d guards"
                  !count);
          (* one phase-report event per preprocessing that rewrote a guard:
             the firing census of the rewrite reads it; decides nothing *)
          if !count > 0 then
            Common.PhaseTime.event_here "tester-normal-form-fired";
          pcsp)
        else pcsp
      in
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
      (* An existential sequence read only through its length and through one
         guarded pointwise condition on its elements (a postcondition "some
         produced sequence has length c and its i-th item is start + i") is
         replaced by its length, its elements by one existential per position
         ([Evaluator.eliminate_pointwise_defined_sequences]): exact in every
         model, and the witness sequence it removes is one no term of the
         clause denotes, so neither the instantiation nor the SMT solver finds
         it.  Its side conditions are small validity questions under a
         resource limit and no wall clock, read only when proved. *)
      (* Two existential sequences read only through their lengths and their
         one concatenation (a nested adapter's postcondition quantifying over
         the items it produces, which its inner adapter reads behind the
         skipped prefix) are merged into one sequence and one length
         ([Evaluator.merge_concatenated_sequence_existentials]): exact in every
         model, and it gives the rewrite above a sequence read only through its
         length and one pointwise condition.  It is tried only on a clause in
         which a sequence binder survives that rewrite and the length-only
         elimination after it, and the rewrite is run again on the merged
         clause: merged on a clause those rewrites already leave without a
         sequence binder, a clause the predicate elimination decided became
         one left to the solving loop (an answer in 0.6 s became one in
         14 s). *)
      let pcsp =
        let pointwise_on =
          config.clauses.eliminate_pointwise_sequence_existentials
        in
        let merge_on = config.clauses.merge_concatenated_sequence_existentials in
        if pointwise_on || merge_on then (
          let count = ref 0 and merged = ref 0 in
          let id = PCSP.Problem.id_of pcsp in
          let fenv = PCSP.Problem.fenv_of pcsp in
          let valid psi =
            match
              Z3Smt.Z3interface.with_rlimit (Some 2_000_000) (fun () ->
                  Z3Smt.Z3interface.check_valid ~timeout:None ~id fenv psi)
            with
            | `Valid -> true
            | _ -> false
          in
          let pointwise phi =
            if pointwise_on then (
              let phi, k =
                Evaluator.eliminate_pointwise_defined_sequences ~valid phi
              in
              count := !count + k;
              phi)
            else phi
          in
          let has_seq_binder phi =
            Set.exists (Formula.quantified_sort_env_of phi) ~f:(fun (_, s) ->
                match s with T_seq.SSeq _ -> true | _ -> false)
          in
          let pcsp =
            PCSP.Problem.map_old pcsp ~f:(fun (uni_senv, phi) ->
                let phi = pointwise phi in
                if
                  merge_on
                  && has_seq_binder (Evaluator.elim_seq_existentials phi)
                then
                  let phi', k =
                    Evaluator.merge_concatenated_sequence_existentials phi
                  in
                  if k = 0 then (uni_senv, phi)
                  else (
                    merged := !merged + k;
                    (uni_senv, pointwise phi'))
                else (uni_senv, phi))
          in
          if merge_on then
            eprintf "[merge-concatenated-sequences] pairs merged: %d\n%!"
              !merged;
          Debug.print
          @@ lazy
               (sprintf "pointwise-defined sequence existentials eliminated: %d"
                  !count);
          pcsp)
        else pcsp
      in
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
        match config.clauses.split_single_cons with
        | Split_single_cons
            { selected_only; outside_upper_bound_probe; outside_early_pins }
          when (not (PCSP.Problem.is_cnf pcsp))
               && (not (outside_upper_bound_probe && !(in_upper_bound_probe ())))
               && not (outside_early_pins && !(in_early_pins_copy ()))
          ->
          let count = ref 0 in
          let pcsp =
            PCSP.Problem.map_old pcsp ~f:(fun (uni_senv, phi) ->
                let uni_senv, phi, n =
                  Evaluator.split_single_cons_free_vars
                    ~selected_only
                    uni_senv phi
                in
                count := !count + n;
                (uni_senv, phi))
          in
          if !count > 0 then single_cons_split_acted () := true;
          Debug.print
          @@ lazy
               (sprintf "single-constructor clause variables split: %d" !count);
          if print_pcsp then (
            Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
            Debug.print @@ lazy "");
          pcsp
        | Split_single_cons _ | No_single_cons_split ->
            (* act census (instrument only): would the selected-only split
               split a clause variable here; nothing computed is used *)
            (if ActCensus.on () && not (PCSP.Problem.is_cnf pcsp) then
               ignore
                 (PCSP.Problem.map_old pcsp ~f:(fun (uni_senv, phi) ->
                      let _, _, n =
                        Evaluator.split_single_cons_free_vars
                          ~selected_only:true uni_senv phi
                      in
                      if n > 0 then
                        ActCensus.note "split_single_cons(selected_only)";
                      (uni_senv, phi))
                   : PCSP.Problem.t));
            pcsp
      in
      let () = stage "elim-unsat-kinds" pcsp in
      let pcsp =
        PCSP.Problem.(
          remove_unused_params
          @@ Common.PhaseTime.with_phase "unsat-wf" (fun () ->
                 elim_unsat_wf_predicates ~print:Debug.print pcsp))
      in
      Debug.print @@ lazy "unsat wf predicates eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let pcsp =
        PCSP.Problem.(
          remove_unused_params
          @@ Common.PhaseTime.with_phase "unsat-nwf" (fun () ->
                 elim_unsat_nwf_predicates ~print:Debug.print pcsp))
      in
      Debug.print @@ lazy "unsat nwf predicates eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let pcsp =
        PCSP.Problem.(
          remove_unused_params
          @@ Common.PhaseTime.with_phase "unsat-parity" (fun () ->
                 elim_unsat_parity_predicates ~print:Debug.print pcsp))
      in
      Debug.print @@ lazy "unsat parity predicates eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let pcsp =
        PCSP.Problem.(
          remove_unused_params
          @@ Common.PhaseTime.with_phase "triv-nwf" (fun () ->
                 elim_triv_nwf_predicate pcsp))
      in
      Debug.print @@ lazy "trivial nwf predicates eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      if print_pcsp then (
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "");
      let pcsp =
        PCSP.Problem.(
          remove_unused_params
          @@ Common.PhaseTime.with_phase "triv-parity" (fun () ->
                 elim_triv_parity_predicate pcsp))
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
        let id = PCSP.Problem.id_of pcsp in
        (* With COAR_SWEEP_DUMP_DIR set, every question of the sweep is kept
           as [DIR/sweep<pid>_<n>_k.smt2] (the solver's assertions, then the
           answer and its seconds once it returns) beside [DIR/sweep<pid>_<n>.fml]
           (the formula as this tree prints it): a diagnostic for replaying a
           question that did not return; nothing is written otherwise. *)
        let dump_dir = Sys.getenv "COAR_SWEEP_DUMP_DIR" in
        let asked = ref 0 in
        let ask_here phi =
          let call () =
            Z3Smt.Z3interface.check_valid ~timeout:(Some 500)
              ~fresh_solver:false ~id (LogicOld.get_fenv ()) phi
          in
          match dump_dir with
          | None -> call ()
          | Some dir ->
              let prefix =
                sprintf "%s/sweep%d_%d" dir
                  (Pid.to_int (Core_unix.getpid ()))
                  !asked
              in
              incr asked;
              Out_channel.write_all (prefix ^ ".fml")
                ~data:(Formula.str_of phi ^ "\n");
              Z3Smt.Z3interface.with_query_dump prefix call
        in
        (* A question whose shape [Z3interface.may_not_return] refuses (a
           quantifier binding a sequence, or a sort reaching one) is not asked
           in this process: Z3's sequence theory has a loop that reads neither
           the 500 ms timeout nor a resource limit, and on such a sweep question
           it stayed open 25-77 s while the process grew to its memory cap,
           which ends the run, though the same question is undecided at 500 ms
           (or proved valid in 0.06 s) in the runs where it returns.

           Sound to skip: the sweep only ever reads [`Invalid] (a countermodel
           refuting the problem); a question left unasked, like one undecided,
           refutes nothing and leaves the clauses as they were, so the problem
           goes on unchanged and every later stage decides it as without the
           sweep.  What is lost is a refutation the in-process question would
           have found, and only on the refused shapes; every other question is
           asked exactly as before.  With [sweep_fork_margin_ms] set a refused
           question is asked in a killed copy instead, where the loop is
           bounded by the kill. *)
        let refused = ref 0 in
        let ask_here_gated =
          PCSatCommon.UnknownFreeSweep.ask_gated
            ~refuse:Z3Smt.Z3interface.may_not_return
            ~on_refused:(fun () ->
              incr refused;
              Common.PhaseTime.event_here "not-asked-shape")
            ~here:ask_here
        in
        (* [unknown_free_clauses.sweep_fork_margin_ms]: the question in a
           killed copy, only its refutation read back; a question that cannot
           be forked is asked here, gated as without the switch *)
        let ask_in_copy m phi =
          match
            Common.PhaseTime.with_phase "forked" @@ fun () ->
            PCSatCommon.ForkedQuery.run_forked
              ~ms:(500 + Int.max m 0)
              (fun () ->
                match
                  Z3Smt.Z3interface.check_valid ~timeout:None
                    ~fresh_solver:false ~id (LogicOld.get_fenv ()) phi
                with
                | `Invalid _ -> true
                | _ -> false)
          with
          | `Value true -> `Invalid []
          | `Value false | `Lost -> `Timeout
          | `Not_forked -> ask_here_gated phi
        in
        let ask =
          match config.unknown_free_clauses.sweep_fork_margin_ms with
          | None -> ask_here_gated
          | Some m -> ask_in_copy m
        in
        let result =
          PCSatCommon.UnknownFreeSweep.sweep
            ~pieces:(fun c -> [ c ])
            ~expired:(fun () ->
              Float.(Common.Clock.now_s () -. started > 5.))
            ~ask formulas
        in
        Debug.print
        @@ lazy
             (sprintf
                "[unknown-free sweep] %s: %d clause(s) without an unknown \
                 (%d not asked, of a shape the solver may not return on): %s \
                 in %.2f s"
                where (List.length formulas) !refused
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
         caller passes [Purpose.Eliminate_keeping]. *)
      let may_refute = Purpose.may_refute purpose in
      (* the refuting stages whose cost is not a few validity questions: the
         refutation by unfolding, the finite instantiation of the quantified
         sorts and the universal-function instances.  A caller that discards
         an [unsat] ([refutation_unread]) skips them; the unknown-free sweeps
         still run, since a sweep is a handful of bounded questions and the
         refutation it gives early would otherwise be found again, more
         slowly, by the zero-unknown verdict of the solve that follows *)
      let may_refute_costly =
        may_refute
        &&
        if !(refutation_unread ()) then (
          Common.PhaseTime.event_here "refutation-stages-unread";
          false)
        else true
      in
      (* set when a sweep refutes, so that neither the later sweep nor the
         finite instantiation is run on the constraint [false] it leaves *)
      let swept_refuted = ref false in
      let pcsp =
        if (not may_refute) || not config.unknown_free_clauses.sweep_before_elimination then pcsp
        else
          match
            Common.PhaseTime.with_phase "unknown-free-sweep" (fun () ->
                sweep_unknown_free ~where:"before the elimination" pcsp)
          with
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
          config.elimination.questions.seq_axiom_fallback.budget_ms
        @@ fun () ->
        PvarEliminator.elim_pvs ~record_resolved_defs:witness.WitnessConfig.sat
          ~elim_one_sided_fn:config.elimination.one_sided_fn_preds
          ~fn_consequences:config.elimination.fn_totality_consequences ~bpvs
          ~set_aside:
            {
              aside_max_clauses = config.elimination.set_aside.max_clauses;
              aside_definitional = config.elimination.set_aside.definitional;
              aside_shared_args =
                (match config.elimination.set_aside.definitional_args with
                | Shared -> true
                | All_free -> false);
              aside_gaining =
                (match config.elimination.set_aside.naming with
                | Gaining_only -> true
                | Every_multiplied -> false);
              aside_trigger = config.elimination.set_aside.trigger_clauses;
            }
          pcsp
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
                Common.PhaseTime.with_phase "unknown-free-sweep" (fun () ->
                    sweep_unknown_free ~where:"before the post-elimination hook"
                      pcsp)
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
      let pcsp =
        Common.PhaseTime.with_phase "unused-params" (fun () ->
            PCSP.Problem.(remove_unused_params pcsp))
      in
      let pcsp =
        if config.clauses.cancel_seq_concat_equations then (
          let pcsp =
            PCSP.Problem.map_old pcsp ~f:(fun (uni_senv, phi) ->
                (uni_senv, Evaluator.cancel_seq_concat_equations phi))
          in
          Debug.print @@ lazy "common prefixes and suffixes of sequence equations cancelled:";
          Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
          pcsp)
        else (
          (* act census (instrument only): would the cancellation change a
             clause; nothing computed here is used *)
          if ActCensus.on () then
            ignore
              (PCSP.Problem.map_old pcsp ~f:(fun (uni_senv, phi) ->
                   if
                     not
                       (String.equal (Formula.str_of phi)
                          (Formula.str_of
                             (Evaluator.cancel_seq_concat_equations phi)))
                   then ActCensus.note "cancel_seq_concat_equations";
                   (uni_senv, phi))
                : PCSP.Problem.t);
          pcsp)
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
        if config.clauses.dedup_alpha_equivalent_disjuncts then
          Common.PhaseTime.with_phase "dedup" (fun () ->
              PCSP.Problem.dedup_alpha_equivalent_disjuncts ~print:Debug.print
                pcsp)
        else pcsp
      in
      (* what the tester normal form leaves behind, on a problem where it
         rewrote a guard: the one-point rule and the elimination act on the
         payloads it named, so an existential the input wrote over a
         constructor application ([exists u. x = C(u) /\ ..]) arrives as a
         one-point existential over a field ([exists u. u = 0 /\ ..]), and two
         copies of a premise merged by the elimination can differ in the order
         of their operands, which the dedup above does not see.  Both are
         removed here ([Evaluator.elim_exists_onepoint], then
         [Evaluator.dedup_ac_operands]), each an equivalence per clause in
         every model, so the problem is the same question in a smaller form.
         Without it, on an input where the normal form rewrote two guards,
         each clause of the preprocessed problem was 16-31 % larger than the
         same clause preprocessed from the selector form, and the refutation
         the selector form gets within 50 s was not found within 120 s; with
         it each clause is smaller than the selector form's or within 1 % of
         it, and the refutation comes in under 20 s.  A problem the normal
         form did not touch is returned as it is. *)
      let pcsp =
        if !tester_guards = 0 then pcsp
        else
          let points = ref 0 and dropped = ref 0 in
          let pcsp =
            Common.PhaseTime.with_phase "tester-normal-form-tidy" (fun () ->
                PCSP.Problem.map_old_changed pcsp ~f:(fun (uni_senv, phi) ->
                    let phi, n = Evaluator.elim_exists_onepoint phi in
                    let phi, m = Evaluator.dedup_ac_operands phi in
                    points := !points + n;
                    dropped := !dropped + m;
                    if n + m = 0 then None else Some (uni_senv, phi)))
          in
          Debug.print
          @@ lazy
               (sprintf
                  "tester normal form tidied: %d one-point existentials, %d \
                   duplicate operands"
                  !points !dropped);
          pcsp
      in
      (* the early duplicate check ([ParallelRace.Duplicate.early]): what
         follows up to the stage that shares determined arguments is
         refutation-only (the unknown-free sweep, the unfolding refutation,
         the finite instantiation), returning this problem unless it refutes
         it, so a raced copy whose problem here is the process's would ask the
         process's refutation questions again; only the outermost solve
         compares, as at the final check *)
      if !PCSatCommon.ParallelRace.Duplicate.early && !(solve_depth ()) = 1 then
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
        else if (not may_refute) || not config.unknown_free_clauses.sweep_before_finite_instances
        then pcsp
        else
          match
            Common.PhaseTime.with_phase "sweep" (fun () ->
                sweep_unknown_free ~where:"before the finite instances" pcsp)
          with
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
         caller finishes before its answer leaves; with [settle_ms], a caller
         whose answer is not a verdict first waits that long from the fork for
         the copy ([ParallelRace.settle_then_finish]). *)
      let stage_raced ?settle_ms ~label ~enabled ~finite_race pcsp body =
        match finite_race with
        | Some races
          when enabled
               && (not (PCSatCommon.SolveDeadline.active ()))
               && Option.is_none (Stdlib.Sys.getenv_opt "COAR_FINITE_EMIT") -> (
            match
              Common.PhaseTime.with_phase (label ^ "-fork") (fun () ->
                  (* [`None]: the copy refutes by a pass the process does
                     not run on its own problem (finite instances, bounded
                     unfoldings), so no inclusion of problems says the
                     process reaches the copy's refutation *)
                  PCSatCommon.ParallelRace.start ~reads:`None
                    ?settle_by:
                      (Option.map settle_ms ~f:(fun ms ->
                           Common.PhaseTime.now () +. (Float.of_int ms /. 1000.)))
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
         [refute_by_unfolding.parallel] it is raced the same way *)
      let pcsp =
        match config.refute_by_unfolding with
        | No_unfolding -> pcsp
        | Unfold _ when (not may_refute_costly) || !swept_refuted -> pcsp
        | Unfold _ when Common.Util.Task.other_domains_live () ->
          (* every resolvent is asked in a forked copy, and OCaml refuses a
             fork while another domain runs (a primal-dual solver's pool), so
             each question would come back undecided and the pass, which only
             an [`Invalid] answer ends with a refutation, could only spend the
             time of building its unfoldings: it is not started.  The result
             is the one the pass would return *)
          Debug.print
          @@ lazy
               "[unfold-refute] not started: another domain is running, so \
                no copy could be forked to ask a resolvent";
          pcsp
        | Unfold u ->
          Common.PhaseTime.with_phase "unfold-refute" @@ fun () ->
          (* raced, the copy is waited for when the process ends with no
             verdict, up to the pass budget from the fork (the copy's pass
             starts its clock a moment later and stops asking there) plus a
             second for the copy to kill its last question and reply *)
          stage_raced ~settle_ms:(u.budget_ms + 1000)
            ~label:"refute-by-unfolding" ~enabled:u.parallel ~finite_race pcsp
          @@ fun () ->
          (* a problem not in clausal form is put in it here: the
             unfoldings read clauses, and the copy is discarded *)
          match
            Common.PhaseTime.with_phase "to-cnf" (fun () ->
                PCSP.Problem.clauses_of_opt (PCSP.Problem.to_cnf pcsp))
          with
          | None -> pcsp
          | Some clauses ->
              let senv = PCSP.Problem.senv_of pcsp in
              (* the clauses in the old representation, for the census and
                 both searches below.  A conversion that drew no fresh name
                 is a function of [senv] and [clauses], so a later use takes
                 the first one's result, which converting again would give
                 structurally equal; one that drew names (or ran inside a
                 replay, where draws do not move the counter) is done again
                 at each use, as each use would draw its own *)
              let convert () =
                Common.PhaseTime.with_phase "to-old-clauses" (fun () ->
                    Set.to_list @@ ClauseSet.to_old_clause_set senv clauses)
              in
              let first_conversion = ref None in
              let old_clauses () =
                match !first_conversion with
                | Some (cls, true) -> cls
                | Some (_, false) -> convert ()
                | None ->
                    let c0 = Atomic.get Ident.tvar_count in
                    let cls = convert () in
                    let reusable =
                      (not (Ident.replaying_fresh_names ()))
                      && Atomic.get Ident.tvar_count = c0
                    in
                    first_conversion := Some (cls, reusable);
                    cls
              in
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
                    (old_clauses ());
                  if String.equal v "only" then Common.ProcessExit.exit 0);
              (* with [refute_by_unfolding.fn_steps], the test reading a step's
                 functional atoms through their totality *)
              let fn_steps_is_fn () =
                if u.fn_steps then
                  Some
                    (fun p ->
                      PCSP.Problem.is_fn_pred pcsp (Ident.pvar_to_tvar p))
                else None
              in
              (* COAR_UNFOLD_EXACT_CENSUS set in the environment: the number of
                 goal resolvents [refute_by_unfolding.exact_levels] would ask
                 (every level, nothing asked, no budget), on stderr, before the
                 pass, and the process then exits: building the levels draws
                 fresh names, which would shift those of everything after it.
                 Whether the pass reaches them depends on the first pass
                 refuting nothing.  An instrument: it decides nothing. *)
              (match Stdlib.Sys.getenv_opt "COAR_UNFOLD_EXACT_CENSUS" with
              | None -> ()
              | Some _ ->
                  let asked = ref 0 in
                  let goals, _ =
                    PCSatCommon.UnfoldRefute.refute_exact_levels
                      ?is_fn:(fn_steps_is_fn ())
                      ?max_size:u.max_size ~solve_linear:u.solve_linear
                      ~linear:u.linear ~depth:u.depth ~max_copies:4096
                      ~expired:(fun () -> false)
                      ~ask:(fun _ ->
                        incr asked;
                        `Unknown "census")
                      (Map.key_set senv) (old_clauses ())
                  in
                  prerr_endline
                    (sprintf "unfold-exact-census: goals=%d would-ask=%d" goals
                       !asked);
                  Common.ProcessExit.exit 0);
              let started = Common.Clock.now_s () in
              (* each resolvent is asked in a forked copy killed at its three
                 questions' budget or at what is left of the pass's budget,
                 whichever is less: Z3's own timeout does not bound a question
                 over sequences, and [expired] is read only between
                 resolvents *)
              let dump_count = ref 0 in
              (* [step_ms], [guess_ms]: the budgets of [ask]'s two questions,
                 the pass's own by default; [budget_ms]: the pass's whole
                 budget, the one the question is killed within *)
              let ask_resolvent ?(step_ms = u.step_ms) ?(guess_ms = u.guess_ms)
                  ?(budget_ms = u.budget_ms) started phi =
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
                  budget_ms
                  - Float.iround_down_exn
                      ((Common.Clock.now_s () -. started) *. 1000.)
                in
                PCSatCommon.UnfoldRefute.ask_forked ~print:Debug.print
                  ~clear_contexts:
                    (match u.contexts with
                    | Inherited_contexts -> false
                    | Cleared_contexts | Cleared_fresh_native -> true)
                  ~fresh_native:
                    (match u.contexts with
                    | Cleared_fresh_native -> true
                    | Inherited_contexts | Cleared_contexts -> false)
                  ?step_ms ~guess_retries:u.guess_retries
                  ?guess_ms
                  ~hoist:u.hoist_bounds
                  ~ms:
                    (Int.max 1
                       (Int.min left (3 * u.timeout_ms)))
                  ~id:(PCSP.Problem.id_of pcsp) phi
              in
              let n, result =
                Common.PhaseTime.with_phase "refute" @@ fun () ->
                PCSatCommon.UnfoldRefute.refute ~print:Debug.print
                  ?is_fn:(fn_steps_is_fn ())
                  ?max_size:u.max_size
                  ?counter_cap:u.counter_depth
                  ~solve_linear:u.solve_linear
                  ~linear:u.linear ~depth:u.depth ~max_copies:4096
                  ~expired:(fun () ->
                    Float.(
                      Common.Clock.now_s () -. started
                      > of_int u.budget_ms /. 1000.))
                  ~ask:(ask_resolvent started)
                  (Map.key_set senv)
                  (old_clauses ())
              in
              Debug.print
              @@ lazy
                   (sprintf
                      "[unfold-refute] depth %d: %d goal resolvent(s): %s in \
                       %.2f s"
                      u.depth n
                      (match result with
                      | Some (i, _, _) -> sprintf "resolvent %d refuted" i
                      | None -> "nothing refuted")
                      (Common.Clock.now_s () -. started));
              let expired () =
                Float.(
                  Common.Clock.now_s () -. started
                  > of_int u.budget_ms /. 1000.)
              in
              let result =
                match result with
                | Some _ -> result
                | None when u.exact_levels && not (expired ()) -> (
                    (* in a forked copy, so that the names the pass draws for
                       its levels do not shift those of the passes after it:
                       with the names shifted, the doubling pass's question on
                       an input this pass cannot touch (no free sequence) was
                       refuted in none of 4 runs where it was in 4 of 4.  Only
                       the index of the refuted goal comes back; the caller
                       reads no more than that a goal was refuted *)
                    let left =
                      u.budget_ms
                      - Float.iround_down_exn
                          ((Common.Clock.now_s () -. started) *. 1000.)
                    in
                    let budget_ms = Int.min left u.exact_levels_budget_ms in
                    let exact_started = Common.Clock.now_s () in
                    let exact_expired () =
                      Float.(
                        Common.Clock.now_s () -. exact_started
                        > of_int budget_ms /. 1000.)
                    in
                    let refuted =
                      Common.PhaseTime.with_phase "refute-exact-levels"
                      @@ fun () ->
                      PCSatCommon.ForkedQuery.run ~ms:(Int.max 1 budget_ms)
                        (fun () ->
                          let n, result =
                            PCSatCommon.UnfoldRefute.refute_exact_levels
                              ~print:Debug.print
                              ?is_fn:(fn_steps_is_fn ())
                              ?max_size:u.max_size
                              ~solve_linear:u.solve_linear
                              ~linear:u.linear ~depth:u.depth
                              ~max_copies:4096 ~expired:exact_expired
                              ~ask:
                                (ask_resolvent
                                   ~step_ms:(Some u.exact_levels_step_ms)
                                   ~guess_ms:(Some u.exact_levels_step_ms)
                                   ~budget_ms exact_started)
                              (Map.key_set senv)
                              (old_clauses ())
                          in
                          (n, Option.map result ~f:fst3))
                    in
                    Debug.print
                    @@ lazy
                         (sprintf
                            "[unfold-refute] exact levels: %s in %.2f s"
                            (match refuted with
                            | Some (n, Some i) ->
                                sprintf "%d goal(s): goal %d refuted" n i
                            | Some (n, None) ->
                                sprintf "%d goal(s): nothing refuted" n
                            | None -> "the copy answered nothing")
                            (Common.Clock.now_s () -. started));
                    match refuted with
                    | Some (_, Some i) -> Some (i, Formula.mk_false (), [])
                    | _ -> None)
                | None -> None
              in
              let result =
                match result with
                | Some _ -> result
                | None
                  when u.fitting_doubling
                       && not (expired ()) ->
                    let n, result =
                      Common.PhaseTime.with_phase "refute-fitting" @@ fun () ->
                      PCSatCommon.UnfoldRefute.refute_fitting
                        ~print:Debug.print
                        ?is_fn:(fn_steps_is_fn ())
                        ?max_size:u.max_size
                        ~solve_linear:u.solve_linear
                        ~linear:false ~depth:u.depth
                        ~max_copies:4096 ~expired ~ask:(ask_resolvent started)
                        (Map.key_set senv)
                        (old_clauses ())
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
          ~enabled:(ConfigSwitch.finite_forall_sorts_parallel config)
          ~finite_race pcsp body
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
          (not (ConfigSwitch.finite_forall_sorts config))
          || (not may_refute_costly)
          || !swept_refuted
          || Set.is_empty svars
          || ((not (ConfigSwitch.finite_forall_sorts_by_name config))
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
             estimate [finite_forall_sorts.max_instance_size] is read against *)
          let problem_size = lazy (PCSP.Problem.ast_size_of pcsp) in
          let refuted_at n =
            match ConfigSwitch.finite_forall_sorts_max_instance_size config with
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
            let proposed_names =
              List.map (Set.to_list svars) ~f:(fun sv ->
                  PCSatCommon.CellQual.finite_sort_instance_name n
                    (Ident.name_of_svar sv))
            in
            let scoped =
              with_finite_instance_scope ~names:proposed_names
                (fun original_dtenv saved_fenv ->
            let () = finite_log (fun () ->
                sprintf "size %d estimate %d" n (Lazy.force problem_size * n)) in
            (* with [finite_forall_sorts_charge_construction], the query's
               budget is a deadline from here, read between the steps that
               build the instance *)
            let deadline =
              if ConfigSwitch.finite_forall_sorts_charge_construction config then
                Some
                  (Common.Clock.now_s ()
                  +. (Float.of_int (ConfigSwitch.finite_forall_sorts_query_timeout config)
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
            let saved_dtenv =
              Map.Poly.fold smap ~init:original_dtenv ~f:(fun ~key:_ ~data env ->
                match data with
                | LogicOld.T_dt.SDT dt -> LogicOld.DTEnv.update_dt env dt
                | _ -> env)
            in
            (* The recursive functions the input declares -- the [SizeOf_…] of
               every datatype -- live in a process-global environment and are
               written over the ORIGINAL sorts.  The formula below has had the
               quantified sort substituted out of it, so handing the solver the
               environment as it stands offers the same function at two
               incompatible sorts and the query is rejected outright.  The
               environment is therefore substituted with the same map. *)

            let dtenv_substituted, fenv_substituted =
              Common.PhaseTime.with_phase "finite-envs" (fun () ->
                  finite_instance_envs smap saved_dtenv saved_fenv)
            in
            (* The scope's finally is already active before either install.
               Local construction above has not modified a global environment. *)
            LogicOld.set_dtenv dtenv_substituted;
            LogicOld.set_fenv fenv_substituted;
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
                     | None -> ConfigSwitch.finite_forall_sorts_query_timeout config
                     | Some d ->
                         let left =
                           Float.to_int
                             ((d -. Common.Clock.now_s ()) *. 1000.)
                         in
                         if left <= 0 then raise Finite_construction_spent
                         else
                           Int.min
                             (ConfigSwitch.finite_forall_sorts_query_timeout
                                config)
                             left))
                ~id:query_id
                fenv_substituted
                [ Formula.mk_and bound expanded ]
              in
              let query = Formula.mk_and bound expanded in
              if
                (ConfigSwitch.finite_forall_sorts_fork_query config)
                && Z3Smt.Z3interface.may_not_return query
              then
                (* the kill is the budget: the solver's own timer is the one
                   that does not hold here *)
                let ms = ConfigSwitch.finite_forall_sorts_query_timeout config in
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
                    ~targeted:(ConfigSwitch.finite_forall_sorts_targeted_instance config)
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
              let instance = substituted_problem () in
              Z3Smt.Z3interface.clear_instance_pool ();
              `Commit (`Emitted instance))
            else
            let t_query = Common.Clock.now_s () in
            let ans =
              Common.PhaseTime.with_phase "finite-query" @@ fun () ->
              try run_query ()
              with Finite_construction_spent ->
                finite_log (fun () ->
                    sprintf "size %d construction past its budget" n);
                `Timeout
            in
            `Restore (`Queried
              (ans, smap, saved_dtenv, saved_fenv, dtenv_substituted,
               fenv_substituted, substituted_problem, t_query)))
            in
            match scoped with
            | None ->
                finite_log (fun () ->
                    sprintf "size %d declined: occupied environment or finite datatype name" n);
                `Undecided
            | Some (`Emitted instance) -> emitted := Some instance; `Undecided
            | Some (`Queried
                (ans, smap, saved_dtenv, saved_fenv, dtenv_substituted,
                 fenv_substituted, substituted_problem, t_query)) ->
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
            | _ when not (ConfigSwitch.finite_forall_sorts_nested_solve config)
              ->
                `Undecided
            (* No nested scope is needed without a solver to hand the instance to. *)
            | _ when Option.is_none solver -> `Undecided
            (* The nested solve owns a separate scope after the ordinary
               query restored its pre-extension environment and released ownership. *)
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
                let solve_instance = Option.value_exn solver in
                let t_nested = Common.Clock.now_s () in
                let nested =
                  with_finite_instance_scope ~reset_pool:true ~names:proposed_names
                    (fun _original_dtenv _original_fenv ->
                    let answer =
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
                         match
                           ConfigSwitch.finite_forall_sorts_nested_solve_budget
                             config
                         with
                         | None -> solve_instance instance
                         | Some ms ->
                             PCSatCommon.SolveDeadline.within
                               ~strict_budget:
                                 (ConfigSwitch
                                  .finite_forall_sorts_nested_solve_strict_budget
                                    config)
                               ?after_first_round:
                                 (Option.map
                                    (ConfigSwitch
                                     .finite_forall_sorts_nested_solve_budget_after_first_round
                                       config)
                                    ~f:(fun ms -> Float.of_int ms /. 1000.))
                               ~seconds:(Float.of_int ms /. 1000.)
                               (fun () ->
                                 if
                                   ConfigSwitch
                                   .finite_forall_sorts_nested_solve_stage_deadline
                                     config
                                 then
                                   (* a stage boundary reached past the
                                      strict deadline ends the nested solve,
                                      which then answers nothing *)
                                   try
                                     PCSatCommon.SolveDeadline.with_stage_check
                                       true (fun () -> solve_instance instance)
                                   with
                                   | PCSatCommon.SolveDeadline.Expired_at_stage
                                   ->
                                     Or_error.error_string
                                       "nested solve past its strict deadline"
                                 else solve_instance instance))
                    in
                    `Restore answer)
                in
                match nested with
                | None -> `Undecided
                | Some answer ->
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
                    | _ -> `Undecided))
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
                    is concluded from them";
              pcsp
          | Some n ->
              Debug.print
              @@ lazy
                   (sprintf
                      "the system has no solution when a quantified sort has \
                       %d element(s), and a solution would have to work for \
                       every type, so it has none"
                      n);
              PCSP.Problem.of_old_formulas ~params:(PCSP.Problem.params_of pcsp)
              @@ Set.Poly.singleton (Map.Poly.empty, Formula.mk_false ())
      in
      let pcsp =
        match config.universal_function_expansion with
        | Some ms
          when may_refute_costly && (not !swept_refuted)
               && not (Formula.is_false (PCSP.Problem.old_formula_of pcsp)) -> (
            match
              Common.PhaseTime.with_phase "universal-instances" (fun () ->
                  refute_by_universal_instances ~ms pcsp)
            with
            | Error reason ->
                Debug.print
                @@ lazy ("[universal instances] nothing concluded: " ^ reason);
                Common.PhaseTime.event "universal-instances/declined";
                pcsp
            | Ok k -> (
              Debug.print
              @@ lazy
                   (sprintf
                      "[universal instances] %d instances of the universal \
                       functions at the constant and at a hole are \
                       unsatisfiable together, so the problem has no solution"
                      k);
              Common.PhaseTime.event "universal-instances/refuted";
              PCSP.Problem.of_old_formulas ~params:(PCSP.Problem.params_of pcsp)
              @@ Set.Poly.singleton (Map.Poly.empty, Formula.mk_false ())))
        | _ -> pcsp
      in
      Debug.print @@ lazy "**************** end elim pvars ****************";
      let pcsp, param_logs =
        if not config.argument_reduction.drop_constant_args then (pcsp, param_logs)
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
        match config.argument_reduction.share_determined with
        | No_share_determined -> (pcsp, param_logs)
        | Share_determined s ->
          let pcsp', added =
            share_determined_pvar_args
              ~budget_ms:s.budget_ms
              ~fallback_cap:s.seq_axiom_fallback_ms
              ~syntactic_first:s.syntactic_first
              ~memo_questions:s.memo_questions
              ~memo_undecided:s.memo_undecided
              ~slice_questions:s.slice_questions
              ~unseen_vacuity:s.unseen_vacuity
              ~collections_only:s.collections_only
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
        match config.argument_reduction.reduce with
        | Reduce { keep_sequences } ->
            DimReducer.keep_sequence_args := keep_sequences;
            PCSP.Problem.remove_unused_params
            @@ DimReducer.elim_pcsp_args ~bpvs param_logs pcsp
        | No_arg_reduction -> pcsp
      in
      let pcsp =
        if config.argument_reduction.drop_fn_copy_args then
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
        if config.clauses.elim_ite then (
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
        if config.clauses.restore_witness_universals then
          PCSP.Problem.(
            remove_unused_params @@ restore_witness_universals pcsp)
        else pcsp
      in
      let pcsp =
        if config.elimination.fn_feeding_fn then
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
        if config.clauses.cancel_seq_concat_equations then (
          let pcsp =
            PCSP.Problem.map_old pcsp ~f:(fun (uni_senv, phi) ->
                (uni_senv, Evaluator.cancel_seq_concat_equations phi))
          in
          Debug.print @@ lazy "common prefixes and suffixes of sequence equations cancelled:";
          Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
          pcsp)
        else (
          (* act census (instrument only): would the cancellation change a
             clause; nothing computed here is used *)
          if ActCensus.on () then
            ignore
              (PCSP.Problem.map_old pcsp ~f:(fun (uni_senv, phi) ->
                   if
                     not
                       (String.equal (Formula.str_of phi)
                          (Formula.str_of
                             (Evaluator.cancel_seq_concat_equations phi)))
                   then ActCensus.note "cancel_seq_concat_equations";
                   (uni_senv, phi))
                : PCSP.Problem.t);
          pcsp)
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
        if config.condensation.final_unknown_free then (
          let pcsp =
            Common.PhaseTime.with_phase "condense-unknown-free" (fun () ->
                condense_final_unknown_free_clauses pcsp)
          in
          Debug.print @@ lazy "unknown-free clauses condensed:";
          Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
          pcsp)
        else pcsp
      in
      let pcsp =
        if config.condensation.final_clauses then (
          let pcsp = condense_final_clauses pcsp in
          Debug.print @@ lazy "final clauses condensed:";
          Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
          pcsp)
        else pcsp
      in
      let pcsp =
        if config.elimination.drop_implied_body_atoms then (
          let pcsp = drop_implied_body_atoms pcsp in
          Debug.print @@ lazy "premises implied by another premise dropped:";
          Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
          if print_pcsp then (
            Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
            Debug.print @@ lazy "");
          pcsp)
        else pcsp
      in
      let pcsp =
        if config.clauses.dedup_alpha_equivalent_clauses then (
          let pcsp, dropped =
            Common.PhaseTime.with_phase "dedup-clauses" (fun () ->
                PCSP.Problem.dedup_alpha_equivalent_clauses pcsp)
          in
          (* an instrument: with [COAR_DEDUP_CLAUSES_TRACE] set, one line on
             stderr per preprocessing that reaches this step, dropped or not,
             so that a census can tell a file where nothing was dropped from
             one that never got here; with the value [exit], the process
             then exits, so that a census pays only for the preprocessing *)
          (match Sys.getenv "COAR_DEDUP_CLAUSES_TRACE" with
          | None -> ()
          | Some v ->
              eprintf "[dedup-clauses] dropped %d of %d\n%!" dropped
                (dropped
                + Option.value_map ~default:0 ~f:Set.length
                    (PCSP.Problem.clauses_of_opt ~full_clauses:false pcsp));
              if String.equal v "exit" then Common.ProcessExit.exit 0);
          if dropped > 0 then (
            for _ = 1 to dropped do
              Common.PhaseTime.event "dedup-clauses/dropped"
            done;
            Debug.print
            @@ lazy
                 (sprintf
                    "dropped %d clause(s) that differ from another only in \
                     binder names"
                    dropped));
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
    let m = config.clauses.cell_abstraction in
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

  (* [clauses.word_ranges]: solve the problem with the inductive ranges of
     its word arguments as premises of the body atoms, and conjoin them to a
     solution ([PCSatCommon.WordRanges] has the argument).  Every answer of
     the strengthened problem is an answer of the given one, so nothing falls
     back. *)
  let solve_with_word_ranges solver pcsp =
    let open Or_error in
    match config.clauses.word_ranges with
    | No_word_ranges -> solver pcsp
    | Word_ranges { timeout_ms = ms } -> (
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
            | res -> res))

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
    LogicOld.unify_negated_linear := config.condensation.unify_negated_linear;
    ClauseOld.condense_up_to_linear := config.condensation.up_to_linear;
    Common.PhaseTime.with_phase "lint-prop-demands" (fun () ->
        lint_negative_prop_demands pcsp);
    let pcsp =
      if config.clauses.relativise_prop_positions then
        Common.PhaseTime.with_phase "relativise-prop" (fun () ->
            PCSP.Problem.relativise_prop_positions pcsp)
      else pcsp
    in
    if config.enable then (
      incr (solve_depth ());
      (fun f -> Exn.protect ~f ~finally:(fun () -> decr (solve_depth ())))
      @@ fun () ->
      let finite_certificate = ref None in
      let finite_race = ref [] in
      let verdict = ref false in
      (* the races are finished, the newest first, however this returns, and
         a copy that was handed the run makes the finishing never return.
         When this returns [sat] or [unsat] ([verdict]) a copy still racing is
         killed: a race left here stands for a refutation-only pass, so a
         sound [sat] means the copy had no refutation to find, and [unsat] is
         the verdict its refutation would give.  Any other outcome (an
         [unknown], an error, an exception) first waits for a copy whose race
         set a settling time -- the unfolding refutation's, until its pass
         budget ends -- so that a refutation the sequential order would have
         found within that budget is still handed the run and printed
         ([ParallelRace.settle_then_finish]); a race that set none, the finite
         instantiation's, is killed at once as before *)
      (fun f ->
        Exn.protect ~f ~finally:(fun () ->
            List.iter !finite_race
              ~f:(PCSatCommon.ParallelRace.settle_then_finish ~verdict:!verdict);
            finite_race := []))
      @@ fun () ->
      (fun f ->
        let result = f () in
        (verdict :=
           match result with
           | Ok ((PCSP.Problem.Sat _ | PCSP.Problem.Unsat _), _) -> true
           | Ok ((PCSP.Problem.Unknown | PCSP.Problem.OutSpace _
                 | PCSP.Problem.Timeout), _)
           | Error _ ->
               false);
        result)
      @@ fun () ->
      let bpvs =
        Set.union bpvs @@ ClauseSet.pvs_of
        @@ PCSP.Problem.stable_clauses_of pcsp
      in
      (* [Split_single_cons {outside_early_pins = true}]: the input is kept
         (only then) for the second, unsplit preprocessing the early relation
         pin may ask for *)
      let unsplit_input =
        match config.clauses.split_single_cons with
        | Split_single_cons { outside_early_pins = true; _ }
          when not !(in_early_pins_copy ()) ->
            Some pcsp
        | Split_single_cons _ | No_single_cons_split -> None
      in
      let input_oracle = oracle in
      let acted = single_cons_split_acted () in
      let acted_before = !acted in
      acted := false;
      let split_acted, (oracle, pcsp) =
        Exn.protect
          ~finally:(fun () -> acted := acted_before)
          ~f:(fun () ->
            let r =
              preprocess ~witness ~purpose:(Purpose.Decide bpvs) ~oracle
                ~normalize_params:true ~finite_certificate ~finite_race ?post_elim
                ~solver:
                  (Some
                     (match nested_solver with
                     | Some nested
                       when ConfigSwitch
                            .finite_forall_sorts_nested_solve_fresh_context
                              config ->
                         nested
                     | _ -> solver ~oracle:None))
                pcsp
            in
            (!acted, r))
      in
      (* the unsplit problem for the early relation pin (see
         [NoUnknownLadder.early_pins_problem]), when the split acted: the same
         input preprocessed again with the split left out, at a deeper solve
         depth (so that no raced copy is compared on it) and with the costly
         refuting stages skipped (the problem the solver is given still has
         them run, and only its refutations are read here), computed at the
         first call and remembered.  [None] when that problem has an unknown
         or is not in clause form, or the preprocessing raised: the pin then
         reads the problem it is given, as without the option *)
      let early_pins_problem =
        match unsplit_input with
        | Some input when split_acted ->
            let memo = ref None in
            let lock = Stdlib.Mutex.create () in
            let compute () =
              let depth = solve_depth () in
              let copy = in_early_pins_copy () in
              let unread = refutation_unread () in
              let saved_copy = !copy and saved_unread = !unread in
              incr depth;
              copy := true;
              unread := true;
              Exn.protect
                ~finally:(fun () ->
                  decr depth;
                  copy := saved_copy;
                  unread := saved_unread)
                ~f:(fun () ->
                  try
                    Common.PhaseTime.with_phase "unsplit-preprocess"
                    @@ fun () ->
                    let _, p =
                      preprocess ~witness ~purpose:(Purpose.Decide bpvs)
                        ~oracle:input_oracle ~normalize_params:true ?post_elim
                        input
                    in
                    if
                      PCSP.Problem.is_cnf p
                      && Map.Poly.is_empty (PCSP.Problem.senv_of p)
                    then (
                      Common.PhaseTime.event_here "unsplit-for-early-pins";
                      Common.ActCensus.note
                        "clauses.split_single_cons.outside_early_pins";
                      Some p)
                    else (
                      Common.PhaseTime.event_here
                        "unsplit-for-early-pins-unusable";
                      None)
                  with exn when not (Common.Timer.is_async exn) ->
                    Debug.print
                    @@ lazy
                         ("[split_single_cons] the unsplit preprocessing for \
                           the early pins raised: " ^ Exn.to_string exn);
                    None)
            in
            Some
              (fun () ->
                Stdlib.Mutex.protect lock (fun () ->
                    match !memo with
                    | Some r -> r
                    | None ->
                        let r = compute () in
                        memo := Some r;
                        r))
        | None when split_acted && Common.ActCensus.on () ->
            (* act census (instrument only): the early relation pin would
               have read the unsplit problem here; [None] leaves it reading
               the problem it is given, as without the census *)
            Some
              (fun () ->
                Common.ActCensus.note
                  "clauses.split_single_cons.outside_early_pins";
                None)
        | Some _ | None -> None
      in
      let slot = PCSatCommon.NoUnknownLadder.early_pins_problem () in
      let saved_slot = !slot in
      slot := early_pins_problem;
      (fun f -> Exn.protect ~f ~finally:(fun () -> slot := saved_slot))
      @@ fun () ->
      (* [races.duplicates] (not [Keep]): a raced copy whose preprocessed problem
         is this one is dropped (see [ParallelRace.Duplicate]); only the
         outermost solve of a process compares *)
      if !(solve_depth ()) = 1 then
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
             if config.clauses.cell_abstraction > 0 then
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
        let phase = Common.PhaseTime.with_phase in
        phase "to-cnf" (fun () ->
            PCSP.Problem.to_cnf
            @@ phase "to-nnf" (fun () ->
                   PCSP.Problem.to_nnf
                   @@ phase "normalize" (fun () -> PCSP.Problem.normalize pcsp)))
      in
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
      if config.clauses.cell_abstraction > 0 then
        solve_with_cell_abstraction (solver ~oracle) pcsp
      else solver ~oracle pcsp
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : PreprocessorType)
