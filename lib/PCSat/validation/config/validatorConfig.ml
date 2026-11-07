(** Configuration of the PCSat validator (its JSON record and loader), a
    library of its own so that the Houdini pre-pass's library can read it
    without depending on the validator. *)

open Core
open Common.Util

type cex_strategy = AllExamples | ExamplesUpTo of int [@@deriving yojson]

(** When a clause's counterexample question comes back undecided -- a
    timeout or [unknown] -- and the clause mentions a sequence, whether it is
    asked once more as the validity of the clause with the sequences an
    uninterpreted sort and axioms about length, reads and concatenation
    ([Z3interface.with_seq_axiom_fallback], under the process-wide
    [seq_axiom_fallback] budget and never longer than the question's own),
    the question then read as [unsat] only when that proves the clause valid;
    any other outcome leaves the undecided answer as it was.  Sound: an axiom
    proof of the clause is a proof of it, so the fallback can only turn an
    undecided question into a decided one and never decides one wrongly.
    Why: the native sequence theory leaves undecided a step that pushes one
    element onto ghost sequences holding a chain
    [forall k < len s. R(s[k], s[k+1])], which the axiom form proves at once;
    the predicate eliminator and the zero-unknown verdict already ask that
    second attempt, the clause checks did not. *)
type clause_axiom_fallback =
  | No_fallback  (** every question is answered as the solver answers it *)
  | Fallback of {
      axiom_first_when_proved : bool; [@default true]
          (** in validation, a problem clause whose counterexample question
              an earlier round's check proved valid only through the axiom
              form (the native question undecided, the axiom form a proof) is
              asked in the axiom form FIRST in every later round: a proof
              there is the answer, and otherwise the question is asked as
              before, without the axiom form a second time.  The same two
              questions are asked, in another order, so the answer is the one
              the default order gives (an axiom proof and a native
              countermodel cannot both exist, both being sound); only the
              time changes.  Why: on a Rust-derived input with composition
              clauses over sequences, the native question ran out of its 5 s
              budget on the same clauses round after round before the axiom
              form proved each in well under a second.  When off, the native
              question is always asked first *)
    }
[@@deriving yojson]

let clause_axiom_fallback_on = function
  | No_fallback -> false
  | Fallback _ -> true

let axiom_first_when_proved = function
  | No_fallback -> false
  | Fallback { axiom_first_when_proved } -> axiom_first_when_proved

(** In validation, which earlier answers a clause question equal, up to the
    names of its bound variables, to an earlier question of the same solve
    gets without being asked.  The clause's own free variables (with their
    sorts) are part of the key, so only the same question is matched. *)
type validation_memo =
  | No_memo  (** every question is asked *)
  | Proved_only
      (** a question an earlier one proved valid gets that answer.  Exact:
          the problem and its definitions do not change within a solve, and
          validity does not depend on bound names.  Only a proof is kept,
          never a countermodel (a new asking may give another one) nor an
          undecided answer.  Why: a candidate that changes some unknowns
          leaves the others, and the clauses over those only, as they were,
          but each round substitutes them with fresh bound names; on a
          Rust-derived input about half of the quantified questions of four
          rounds were such repeats *)
  | Proved_and_undecided
      (** as [Proved_only], and a question an earlier round left undecided
          under the same budget is answered [`Timeout] without being asked.
          NOT exact: Z3 is not deterministic across contexts, and a question
          once undecided was observed decided on a later asking; such a later
          proof or countermodel is lost (the candidate is rejected and
          nothing learnt from the clause, as for any undecided answer) *)
[@@deriving yojson]

(** which sequence elements of a counterexample's substitution are opened
    one position at a time *)
type seq_elements =
  | No_seq_elements  (** none: a sequence is kept or dropped whole *)
  | All_clauses
      (** open, one position at a time, the elements of the sequence literals
          in a counterexample's substitution, keeping an opened element only
          while every example the substitution produces stays UNGUARDED --
          the test [examples.partial_model.examples] keeps a dropped variable by, one
          level finer.  A variable whose value is a sequence can otherwise
          only be kept or dropped whole, so an element the clause never reads
          stays at whatever value the model gave it, and a refutation that
          needs that element at one particular value waits for the model to
          happen to choose it.  Needs [parametric_examples]; independent of
          [examples.partial_model.examples] and applied after it when both are on. *)
  | Goal_clauses_only
      (** the same opening, applied only to the examples of a GOAL clause --
          one whose examples have no positive atom, i.e. no head predicate
          application -- and never to a fact or step clause's examples, which
          stay exactly as with the opening off.  Turns the opening on by
          itself (with [parametric_examples]).

          Why only there: resolution binds an example's parameters only by
          syntactic unification, so a positive whose element is a parameter
          no longer meets a step clause's body at the literal the chain
          needs, and the forward positives a refutation walks along are not
          derived. A negative is where the chain ends, so no positive chain
          depends on its elements. Contract as for the opening: every opened
          example is unguarded, and the model's point is an instance of it. *)
[@@deriving yojson]

(** how much of a counterexample's model an example keeps *)
type partial_model = {
  examples : bool; [@default false]
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
  settle_pure : bool; [@default false]
      (** with [examples.partial_model.examples], decide whether a variable may be
          left open by asking the guard discharge (a validity question,
          1 s) whether the clause's predicate-free disjuncts are false for
          every value of the open variables, before the clausal form splits
          them ([ExClauseSet.settle_pure_disjuncts]).  The evaluator alone
          cannot see that [0 <= -1 - x /\ x >= 0] is false, and the clausal
          form makes it two satisfiable guards; a witness's value that the
          clause does not need then stays at the model's point, one new
          example per value.  [false]: the evaluator's test only *)
  seq_elements : seq_elements;
      [@default Common.Util.config_default seq_elements_of_yojson {|["No_seq_elements"]|}]
  group_equal_values : bool; [@default false]
      (** open, as ONE fresh parameter, a group of a counterexample's
          variables the model gave one value (same sort, structurally equal
          value), keeping the replacement only while every example produced
          stays UNGUARDED -- the test [examples.partial_model.examples] keeps a dropped
          variable by. A class is tried whole and, if refused, split into the
          subsets the clause's own equations connect. Dropping one variable at
          a time cannot open two variables a clause equates, since each single
          removal leaves the equation as a guard; opened together the equation
          is settled. Applies to every clause (fact, step, goal), after
          [examples.partial_model.examples] and before the element opening. Needs
          [parametric_examples]. Sound: one parameter for several universally
          quantified clause variables is an instance of the clause's universal
          closure, so an unguarded result is a consequence of the clause, and
          the model's point is an instance of it. *)
  fact_examples : bool; [@default false]
      (** when a candidate violates a FACT clause, keep BESIDE the model's
          point its maximally partial form: the point with every assignment
          dropped that the clause's pure part does not need, one at a time,
          each kept dropped only while the example stays unguarded (the
          test of [examples.partial_model.examples], applied to fact clauses and
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
          does not; with [examples.partial_model.examples] on it adds nothing. *)
}
[@@deriving yojson]

(** asking a counterexample's model again for values that vary *)
type diversify = {
  arrays : bool; [@default false]
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
  at_clause_read_indices : bool; [@default false]
      (** Where [examples.diversify.arrays] asks a constant integer-indexed array to
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
  sequences : bool; [@default false]
      (** The sequence counterpart of [examples.diversify.arrays]: when a
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
  arms : bool; [@default false]
      (** when a counterexample falls in the same arm of a top-level
          disjunction of the query as the last counterexample of a query with
          the same disjunction did, ask the query again restricted to each
          other arm in turn, keeping the first model unless one answers
          [Sat].  A solver keeps answering one arm of a clause's disjunctive
          premise (one branch of a transition relation), so every example
          comes from one branch and a refutation that needs a step of another
          branch (a cycle through an up and a down step) is not sampled.  It
          only chooses which counterexample is used, so it cannot change a
          verdict. *)
  scalars : bool; [@default false]
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
  rationals : int option; [@default Some 64]
      (** [Some n]: when a counterexample gives a real variable a value whose
          denominator exceeds [n], replace it by the simplest rational near
          it (floor, ceiling or a continued-fraction convergent) that the
          evaluator finds keeps the query true, and ask the query again with
          those variables pinned, keeping the first model unless the pinned
          query answers [Sat].  A linear solver answers with a vertex of the
          query's region, a ratio of the candidate's coefficients, which were
          fitted to the earlier examples' values; so the values of one round
          are built from those of the round before and can grow by about a
          hundred digits a round until a template question over them does not
          return within its budget.  It only chooses which counterexample is
          used, so it cannot change a verdict.  [None] asks nothing.
          Default [Some 64]: on a QFL input whose runs stalled when the values
          grew, a bound of 64 answered in every run within 4 s and pinned 6-8
          counterexamples a run, while a bound of 2^20 let the values grow to
          seven digits first and answered 2 runs of 3 in 52-90 rounds. *)
}
[@@deriving yojson]

(** what is read out of a counterexample's model and recorded beside its
    examples *)
type record = {
  cell_witnesses : bool; [@default false]
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
  head_witnesses : bool; [@default false]
      (** When a clause with a predicate in its head yields a counterexample,
          read out of the model the index at which the candidate's read-back
          [forall j. phi] failed in that head (the existential of its negation,
          skolemised as for [examples.record.cell_witnesses]) and record it beside each
          positive example the counterexample produces, in the side table
          [GoalReads] (its head-witness part), never in the example.

          The synthesizer's celled expansion of that example's head reads it
          ([cells.head_at_witnesses]).  Without it, a positive example over a
          constant array is demanded only at the prefix [0 .. 5], and a
          candidate false only below zero or past the prefix is refuted with
          the same point round after round.  Unlike [examples.record.cell_witnesses],
          whose pool is offered to every atom of every example, the index
          reaches only the example its refutation produced, and only its head.
          Every recorded index is a true index of the example's array, so the
          expansion that offers it states one more consequence of the
          example. *)
  goal_reads : bool; [@default true]
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
  premise_instances : bool; [@default false]
      (** carry a premise the clause states with a quantifier into the
          examples derived from it, instantiated at the counterexample's own
          terms. Synthesis learns only from examples and an example is two
          sets of atoms, so a premise the clause states is invisible to it:
          the candidate is asked to satisfy the examples everywhere, not only
          where the premise holds, and Validation then rejects it for a
          situation the premise excludes. *)
}
[@@deriving yojson]

(** the projected regions of counterexamples: beside the point example, the
    counterexample's cell with every variable that is not an argument of an
    unknown application projected out *)
type projected_regions =
  | No_projected_regions  (** a point example only *)
  | Projected_regions of {
        timeout_ms : int; [@default 1000]
            (** the solver budget of the per-example validity question (the
                region implies that some value of the projected variables
                falsifies the candidate-substituted clause), a kill bound: a
                question left undecided only costs the region *)
    }
      (** record, beside the point example of a counterexample, the example
          [forall xK. G(xK) => atoms(xK)], [xK] the variables of the atoms'
          arguments and [G] a model-based projection of the counterexample's
          cell onto them, kept only when Z3 proves [G] implies that the clause's
          other variables can be chosen to falsify the candidate-substituted
          clause (so the example follows from the clause and every point of the
          region refutes the candidate).  The point stays: a consumer that
          grounds parameters at a default point reads a region excluding that
          point as saying nothing. *)
[@@deriving yojson]

(** the regions of counterexamples to a clause on a well-founded unknown *)
type wf_regions =
  | No_wf_regions  (** a point example only *)
  | Wf_regions of {
        timeout_ms : int; [@default 1000]
            (** the solver budget of the validity question above, a kill bound:
                the question is a linear implication, and one left undecided only
                costs the region *)
    }
      (** beside the point example of a counterexample to a clause with a
          positive atom on a well-founded unknown, record the
          counterexample's region (which contains the point, and which a
          reader of regions reads instead of it): the clause's atoms guarded by the model-based cell of the
          negated, candidate-substituted clause at the model (the literals the
          model makes true, a true side of each disjunction), over every
          variable of the clause as a parameter.  Kept only when the cell is a
          conjunction of linear comparisons and Z3 proves it implies both the
          negated pure part (so the example follows from the clause) and the
          negated clause under the candidate (so every point of the region
          refutes the candidate).  For a synthesiser that reads a well-founded
          unknown's examples as regions; a point it reads only as a point. *)
[@@deriving yojson]

(** how a counterexample to a candidate becomes examples (the strategy and
    the lower-bound check, [cex_strategy] and [check_part_sol_with_lbs], stay
    at the validator's top level) *)
type examples = {
  partial_model : partial_model;
      [@default Common.Util.config_default partial_model_of_yojson "{}"]
  diversify : diversify;
      [@default Common.Util.config_default diversify_of_yojson "{}"]
  record : record; [@default Common.Util.config_default record_of_yojson "{}"]
  wf_regions : wf_regions;
      [@default Common.Util.config_default wf_regions_of_yojson {|["No_wf_regions"]|}]
  projected_regions : projected_regions;
      [@default
        Common.Util.config_default projected_regions_of_yojson
          {|["No_projected_regions"]|}]
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
  fn_results_open : bool; [@default false]
      (** add, beside the model's point, the example with the variables of a
          violated clause that are only the result of one premise
          application of a functional unknown ([ExClauseSet.fn_result_vars])
          left open as parameters.  The model gives each such variable the candidate's own
          value, so the point example says only that one witness must move
          off one point; the open example is the clause instance at the
          model's other values, which a synthesizer reading the witness's
          template as a graph turns into the clause's demand at those
          arguments ([fn_result_one_point] of the template synthesizer, meant
          to be switched with this one: under the default reading of
          parametric examples an open integer is grounded at a dummy, which
          is why the point is kept).  Needs [parametric_examples]. *)
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
}
[@@deriving yojson]


(** the two budgets of piece-by-piece validation ([questions.by_pieces]) *)
type by_pieces = { axiom_ms : int; native_ms : int } [@@deriving yojson]

(** the counterexample question of each problem clause *)
type clause_check = {
  cvc5_retry_ms : int option; [@default None]
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
  seq_axiom_fallback : clause_axiom_fallback;
      [@default Fallback { axiom_first_when_proved = true }]
      (** whether a clause's counterexample question (the Houdini pre-pass's
          questions and the validation of a candidate alike) that comes back
          undecided is asked once more in the sequence-axiom form, and in
          which order in later rounds (see [clause_axiom_fallback]) *)
}
[@@deriving yojson]

(** the exact rewrites a validation question is asked through *)
type validation_rewrites = {
  onepoint : bool; [@default true]
      (** each validation clause question that still has a binder is asked
          after the one-point rule and the binder splits of
          [Evaluator.elim_onepoint_and_split_binders]: a bound variable a
          top-level equation of its binder's body fixes is replaced by the
          term it equals.  Exact: the rewritten question is equivalent to
          the original in every model and has no free variable the original
          lacks, so a model of its negation is a counterexample of the
          original.  Why: a [let] in the input reaches the clause as
          [exists x. x = t /\ phi], and on a question whose bound integer
          is fixed by [0 = -3 + x] and then read through [int_to_bv] and
          sequence reads, Z3 answered nothing within 20 s while the same
          question with the bound variables eliminated (z3's [qe-light]
          tactic) was unsat in 0.1 s.  The integer binders a pair of
          constant bounds confines to one value (the indices of a sequence
          of length one, [forall i. 0 <= i < 1 -> ..]) are eliminated
          too.  The question keeps the budget it had as built.  Off: asked
          as built (the default is on since 2026-10-20). *)
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
  seq_pointwise_extract : bool; [@default true]
      (** each validation clause question that still has a binder is asked
          with every universal [forall k. k < 0 \/ k >= len a \/ a[k] =
          b[k + t]] replaced by [(B /\ a = extract b t (len a)) \/ (not B
          /\ the universal)], [B] saying the slice is inside [b]
          ([Evaluator.seq_pointwise_eqs_as_extract]).  Exact: equivalent in
          every model, no variable added, so a model of the rewritten
          negation is a counterexample of the original.  Why: Z3 does not
          find sequence extensionality through the quantifier -- a question
          whose premises say a sequence agrees pointwise with a slice of
          another and whose goal says they differ ran 60 s past its 5 s
          budget in process (25 s standalone without an answer), and with
          the equation written as an [extract] it is unsat in 0.1 s.  Off:
          asked as built. *)
  unfold_eliminable_apps : bool; [@default false]
      (** each validation clause question is asked with every application
          of a defined function that one unfolding step removes unfolded
          ([Evaluator.unfold_eliminable_apps]: a selector or tester over a
          recursive call under a constructor, an equation with a constructor,
          an application at arguments that decide its guard -- whenever the
          step leaves fewer applications than it found).  Exact: each
          step instantiates a definition's equation, which every model of the
          problem satisfies, so the question asked has the same models; the
          counterexample returned is a model of the original question.  Why:
          a candidate built from atoms such as [hd (append x y)] makes a
          question Z3 decides only by unfolding the recursive definition
          under growing depth bounds, whose cost is heavy-tailed (0.1 s to
          over 60 s on one question by seed and history), while one step
          leaves it recursion-free.  Off: asked as built. *)
}
[@@deriving yojson]

(** the readback of a quantified question *)
type readback = {
  instantiate_universals : bool; [@default false]
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
  retry_undecided_forms : bool; [@default false]
      (** with [questions.readback.instantiate_universals], ask an instantiated form
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
  subst_definitions : bool; [@default false]
      (** with [questions.readback.instantiate_universals], ask each instantiated form
          with the variables its top-level disequations define substituted
          away and the result simplified (an identity for validity), so
          that the simplifier's store rules can close what the form states
          about composed writes.  A composition clause over three sequences,
          whose form Z3 4.15.2 decided in 0.2 s, was not decided by Z3 5.1.0
          in 20 s; its substituted form is decided by the simplifier.  When
          off, the forms are asked as they are built. *)
}
[@@deriving yojson]

(** which questions a forked copy asks *)
type fork_scope =
  | Refused_shapes  (** those [may_not_return] refuses *)
  | All_quantified
      (** with [questions.unreturnable], ask in a killed copy every
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
          for the refused shapes.  Off by default: on the Rust-derived inputs it
          acts on it lost no answer, gave no other verdict and gained none, so
          no answer is known to need it.  When off, only the refused shapes
          are forked. *)
[@@deriving yojson]

(** where a question the solver may not return from is asked *)
type unreturnable =
  | In_process  (** in this process, under the solver's own timer *)
  | Forked of {
      scope : fork_scope;
          [@default Common.Util.config_default fork_scope_of_yojson {|["Refused_shapes"]|}]
        kill_ms : int option; [@default None]
            (** with [questions.unreturnable], the wall-clock budget after which
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
    }
      (** ask a counterexample query that binds a sequence under a
          quantifier ([may_not_return]) in a forked copy of the process,
          killed when the query's budget runs out ([questions.quantified_timeout_ms],
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
[@@deriving yojson]

(** the scoped attempt before a quantified validation question *)
type scoped_first =
  | No_scoped_first
  | Scoped_first of {
        budget_ms : int; [@default 1000]
            (** the scoped ask's budget, in ms, capped by the query's own *)
    }
      (** ask a quantified counterexample query that is asked in this
          process first with its negated clause inside a scope of the
          pooled solver ([Z3interface.check_sat_scoped_first]), under
          [questions.scoped_first.budget_ms], and only when that leaves
          it undecided, as it is asked without the switch (then the
          sequence-axiom fallback as before).  Unscoped, Z3 answers such a
          query in a pushed context with its bare [smt] tactic; scoped, with
          its incremental core, which decided validation questions over
          sequences and datatypes in 0.1 s that the tactic left undecided at
          5 s, and leaves others undecided that the tactic decides, which is
          why it comes first and short.  Its [unsat] and [sat] are read as
          the unscoped ask's are.  Not applied to a shape [may_not_return]
          refuses nor to a query asked in a forked copy.  Off by default. *)
[@@deriving yojson]

(** weakening a question [may_not_return] refuses *)
type weaken =
  | No_weaken
  | Weaken of {
        keep_cells : bool; [@default false]
            (** with [questions.weaken], keep asking a truth-table cell
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
    }
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
[@@deriving yojson]

(** how a validation question is asked *)
type questions = {
  timeout_ms : int option; [@default None]
  quantified_timeout_ms : int option; [@default Some 5000]
      (** the budget, in milliseconds, of a validation query whose clause
          still contains a quantifier after the candidate is substituted --
          a candidate read back from array or sequence cells puts a universal
          over the cell index into every clause it occurs in, and a premise
          universal stays universal in the counterexample query, which the
          solver can take minutes over.  Only such queries get this budget
          (the smaller of it and [questions.timeout_ms]); a quantifier-free query keeps
          [questions.timeout_ms].  A query cut by it is undecided, which rejects the
          candidate and learns nothing from that clause while the other
          clauses' counterexamples are still drawn, so it can cost an answer
          (a correct quantified candidate that needs longer to validate is
          proposed again) and never gives a wrong one: [sat] is reported only
          when every query came back unsatisfiable.  Measured on a Rust-derived
          sequence loop, such queries ran 40-136 s each and a 5 s budget on all
          validation queries raised its refutation from 3 of 10 runs to 7 of
          10.  [None] removes the budget. *)
  memo : validation_memo; [@default Proved_only]
      (** which validation answers of this solve are kept and given to a
          later question equal to an earlier one up to the names of its bound
          variables (see [questions.memo]) *)
  read_instances_first_ms : int option; [@default None]
      (** in validation, a clause question that still has a quantifier is
          first asked, by a forked copy within this budget, as its negation
          with each integer universal replaced by its instances at the
          positions the question's ground sequence reads and its function
          applications give, the universal dropped
          ([Ast.QuestionRewrites.int_universals_at_positions]).  The form is
          implied by the negation, so only an [unsat] is read: the clause is
          proved ([`Unsat]) without the ordinary route; anything else asks
          the ordinary route as before.  Sound, not the same answers: it
          proves clauses the ordinary route leaves undecided, and it costs
          up to the budget on a clause it does not prove.  A proof is kept by
          [questions.memo] like any other.  Why: on a bit-set input the same
          clause question (up to bound names) was left undecided in every
          round, each asking about 12 s against a 5 s budget, while its
          negation with the empty sets' zero-word and bit-range premises at
          word 0 was [unsat] in 0.2-0.4 s.  [None]: not asked. *)
  by_pieces : by_pieces option; [@default None]
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
  range_pins : int list; [@default []]
      (** in validation, a quantified clause question that every other route
          left undecided is asked again with each bounded integer existential
          of the question pinned to each width of the list in turn
          ([Ast.RangePin.pinned_question]: [hi = lo + width] assumed, and the
          existential replaced by its [width] instances), and the first
          countermodel is returned as the counterexample.  Only a countermodel
          is read: it is one of the clause's negation, so the answer is sound;
          a pinned question proved valid says nothing and leaves the clause
          undecided.  Each try has the question's own budget.  Why: a goal
          clause stating that two sequences disagree on some bit of an index
          range has a universal over the bit index in its negation, which Z3
          left undecided at 30 s and answered in 0.1 s once the range's width
          was fixed, so every candidate was rejected with nothing learnt.
          [[]]: not asked *)
  defer_undecided : bool; [@default false]
      (** in validation, the problem clauses whose counterexample question
          an earlier round left undecided are asked after every other
          clause, and not asked at all when a clause asked before them has
          already given a counterexample: the candidate is rejected then
          whatever they answer, and an undecided answer adds no example.
          NOT exact: a deferred clause that this round would have refuted
          gives no counterexample, so the round learns fewer examples (never
          a wrong one).  When off, every clause is asked. *)
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
  clause_check : clause_check;
      [@default Common.Util.config_default clause_check_of_yojson "{}"]
  rewrites : validation_rewrites;
      [@default Common.Util.config_default validation_rewrites_of_yojson "{}"]
  readback : readback; [@default Common.Util.config_default readback_of_yojson "{}"]
  unreturnable : unreturnable;
      [@default Common.Util.config_default unreturnable_of_yojson {|["Forked", {}]|}]
  scoped_first : scoped_first;
      [@default Common.Util.config_default scoped_first_of_yojson {|["No_scoped_first"]|}]
  fresh_context_quantified : bool; [@default false]
      (** ask a counterexample query that holds a quantifier, when it is
          asked in this process, as the Z3 interface's measurement mode
          (COAR_Z3_ALWAYS_FRESH=1) asks every quantified query, but for this
          phase only: in a Z3 context of its own, in negation normal form,
          with the definitions it reaches ([Z3interface.check_sat_fresh]; a
          reset clean context under PCSat's [z3.pool = Clean_pool]), instead of
          first in the pooled context every other query shares and, when
          that answers [unknown], again in a context of its own (the
          interface's retry, always on).  A shape that check refuses ([may_not_return])
          is asked in the pooled context as before.  The question is the same
          (negation normal form is an equivalence), so a decided answer means
          the same; which questions are decided within the budget can
          differ.  Off by default. *)
  weaken : weaken; [@default Common.Util.config_default weaken_of_yojson {|["No_weaken"]|}]
  arrays_as_functions : bool; [@default true]
  array_pointwise_elim : bool; [@default true]
      (** ask a counterexample query whose integer arrays are constrained
          only cell by cell -- read at ground indices and at the variable of
          a top-level universal -- with those arrays eliminated
          ([Ast.ArrayPointwise]: an equisatisfiable rewrite whose models
          read back to the query's), before asking it as before *)
}
[@@deriving yojson]


type t = {
  verbose : bool; [@default false]
  parametric_candidates : bool; [@default true]
      (* whether parametric candidate solutions are enabled *)
  parametric_examples : bool; [@default true] (* whether parametric examples are enabled *)
  strategy_synthesis : bool; [@default false] (* require that parametric_examples = true*)
  questions : questions; [@default Common.Util.config_default questions_of_yojson "{}"]
      (** how a validation question is asked *)
  houdini : HoudiniConfig.t;
      [@default Common.Util.config_default HoudiniConfig.of_yojson "{}"]
      (** the Houdini pre-pass: its schedule against the CEGIS loop, its
          candidate families and quotas, how its fixed point asks its
          questions, and its final check ([HoudiniConfig]) *)
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
  cex_strategy : cex_strategy; [@default AllExamples]
  check_part_sol_with_lbs : bool; [@default false]
  examples : examples; [@default Common.Util.config_default examples_of_yojson "{}"]
      (** how a counterexample to a candidate becomes examples *)
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
}
[@@deriving yojson]

(** The flat values the counterexample code reads, unfolded from the variants
    of [examples].  Contract: under every choice each function returns the
    value the former flat field held, and where the choice makes a parameter
    inert its default. *)
module ExamplesSwitch = struct
  let partial_seq_elements c =
    match c.examples.partial_model.seq_elements with
    | No_seq_elements -> false
    | All_clauses | Goal_clauses_only -> true

  let partial_seq_elements_goal_only c =
    match c.examples.partial_model.seq_elements with
    | Goal_clauses_only -> true
    | No_seq_elements | All_clauses -> false

  let wf_region_examples c =
    match c.examples.wf_regions with Wf_regions _ -> true | No_wf_regions -> false

  let wf_region_examples_timeout_ms c =
    match c.examples.wf_regions with
    | Wf_regions { timeout_ms } -> timeout_ms
    | No_wf_regions -> 1000

  let projected_region_timeout_ms c =
    match c.examples.projected_regions with
    | Projected_regions { timeout_ms } -> Some timeout_ms
    | No_projected_regions -> None
end

(** The flat values the validation questions' code reads, unfolded from the
    variants of [questions], and the variants built from flat values.
    Contract: under every choice each function returns the value the former
    flat field held, and where the choice makes a parameter inert its
    default. *)
module QuestionsSwitch = struct
  let validation_by_pieces c =
    Option.map c.questions.by_pieces ~f:(fun p -> (p.axiom_ms, p.native_ms))

  let fork_unreturnable_queries c =
    match c.questions.unreturnable with Forked _ -> true | In_process -> false

  let fork_quantified_queries c =
    match c.questions.unreturnable with
    | Forked { scope = All_quantified; _ } -> true
    | Forked { scope = Refused_shapes; _ } | In_process -> false

  let fork_unreturnable_kill_ms c =
    match c.questions.unreturnable with
    | Forked { kill_ms; _ } -> kill_ms
    | In_process -> None

  let scoped_first_quantified_validation c =
    match c.questions.scoped_first with
    | Scoped_first _ -> true
    | No_scoped_first -> false

  let scoped_first_quantified_validation_ms c =
    match c.questions.scoped_first with
    | Scoped_first { budget_ms } -> budget_ms
    | No_scoped_first -> 1000

  let weaken_unreturnable_queries c =
    match c.questions.weaken with Weaken _ -> true | No_weaken -> false

  let weaken_unreturnable_keep_cells c =
    match c.questions.weaken with
    | Weaken { keep_cells } -> keep_cells
    | No_weaken -> false

  let unreturnable_of ~fork ~quantified ~kill_ms =
    if fork then
      Forked
        { scope = (if quantified then All_quantified else Refused_shapes); kill_ms }
    else In_process

  let scoped_first_of ~on ~budget_ms =
    if on then Scoped_first { budget_ms } else No_scoped_first

  let weaken_of ~on ~keep_cells = if on then Weaken { keep_cells } else No_weaken
end

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
