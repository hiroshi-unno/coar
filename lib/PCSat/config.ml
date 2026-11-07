open Core
open Common.Util
open Coordination
open Preprocessing

(** Which raced copies are stopped because their problem is the process's own.
    A probe raced in a forked copy whose problem, once preprocessed, is the
    problem the process solves (up to fresh names) asks the process's
    questions one for one -- on a Rust-derived input whose unknowns
    preprocessing eliminates, the true-precondition copy asked all 310 of the
    process's solver checks, in the same order, for the whole run -- so on a
    loaded machine it halves the process's speed and gives nothing the
    process does not.  Such a copy is dropped: it leaves, or the process kills
    it, whichever side reaches the comparison second
    ([PCSatCommon.ParallelRace.Duplicate]).  Only a copy is stopped, never an
    answer; the process's answers are the sequential order's with the probe
    finding nothing. *)
type race_duplicates =
  | Keep  (** every raced copy runs to its end *)
  | Drop_at_end
      (** compare a copy's problem with the process's after the whole
          preprocessing *)
  | Drop_early_and_end
      (** compare also right after the predicate elimination, before the
          refutation-only passes that follow it (the unknown-free sweep, the
          unfolding refutation, the finite instantiation), which return the
          problem they are given unless they refute it.  A copy found a
          duplicate there leaves before asking those passes' questions a
          second time; one that is not is compared again after the whole
          preprocessing.  Why: on two Rust-derived inputs the
          true-precondition copy, found a duplicate after the whole
          preprocessing, had spent most of it in those passes (about ten of
          fifteen seconds at idle) beside the process doing the same.  The
          default. *)
[@@deriving yojson]

type races = {
  duplicates : race_duplicates; [@default Drop_early_and_end]
  two_claims : bool; [@default false]
      (** a raced copy that takes the computation over with something other
          than a final answer (the Houdini copy with a failed fixed point's
          counterexamples, which then runs the CEGIS loop again) no longer
          locks out a later copy holding a final answer (a probe's [sat]): the
          right to take over the computation and the right to print the
          verdict are claimed apart, the second at the point the verdict is
          printed, and the first holder of a final answer to claim it prints
          the verdict while the process kills the copy that only took over
          ([PCSatCommon.ParallelRace], "Two claims").  Exactly one verdict is
          printed and every one is a raced copy's or the process's own, as
          before.  [false]: the first copy to claim is given the whole run *)
}
[@@deriving yojson]

(** How the SMT-LIB reader inserts [:law] premises, and when PCSat reads an
    [.smt2] input under the switches that ask for a second reading.  A
    [:law] premise of a universal function is always inserted also into
    every assertion that applies an unknown depending on that function (the
    reader's own reading, the one the laws state); nothing here changes
    that. *)
type laws = {
  dedup_premises : bool; [@default true]
      (** the SMT-LIB reader inserts each [:law] premise without the conjuncts
          the assertion already assumes (another function's copy of the same
          law, a conjunct the law repeats, an antecedent the clause already
          has): the same problem up to [c /\ c = c], with fewer quantified
          premises.  It is the reader's default; with an [.smt2] input,
          [false] re-reads the input with every law inserted whole, once per
          function reaching the assertion, and solves that instead
          ([check_solution] checks against the re-read problem) *)
  read_once : bool; [@default true]
      (** with an [.smt2] input and [-p pcsp], set the reader's switches that
          [dedup_premises] and the [reader]'s
          [onepoint_constructor_binders] ask for before the input is first
          read, and keep that problem instead of reading the input a second
          time for them.  The problem is the one the second reading gives, up
          to fresh names.  The first reading also keeps its assertions until
          the [reader]'s [define_forced_true] has asked which unknowns every
          solution makes [true], and that reading is made only when the answer is not empty
          (an empty answer discards it).  On by default: the problem kept is
          the re-reading's, digest for digest and with the same fresh names
          drawn when both readings start from the same counters.
          [false]: read as given, then read again when a switch asks for it *)
}
[@@deriving yojson]

(** How PCSat reads an [.smt2] input: the readings it makes beside the input
    as written (the forced-true reading, the premise naming), the rewrites the
    reader applies, and the [:law] premises. *)
type reader = {
  define_forced_true : bool; [@default true]
      (** with an [.smt2] input file, read it again with every unknown that
          every solution makes [true] defined as [true]
          ([PCSP.Parser.forced_true_unknowns]: an assertion one of whose
          disjuncts is [forall y. P(y)], or a conjunction with it, while every
          other disjunct is a negated nullary unknown already forced or is
          pure and can be falsified at once in every model), and solve that
          INSTEAD of the problem as given: the two are equivalent, so [sat]
          (extended with the [true]s) and [unsat] are both read.  The point is
          that the definition is made before the reader skolemises the body
          universals over such an unknown into functional witnesses.  [false]:
          no such reading *)
  onepoint_constructor_binders : bool; [@default true]
      (** each existential in
          effect that has an unknown under it is first rid of the bound variables
          a conjunct of its body fixes through constructor applications
          ([PCSP.Problem.elim_constructor_points]: [exists q. v = C(q) /\ phi]
          is [is_C v /\ phi[sel_C v / q]] in every model), so that no
          functional predicate is made for a witness the theory already
          determines.  The reader applies it by default (in every reader that
          builds a constraint problem, not only PCSat's), and the result is
          equivalent to the problem as written, so both verdicts are read.
          [false]: the input is read again without it *)
  fold_inlined_selector_reads : bool; [@default false]
      (** inlining a [define-fun] call, a selector the body applies to a formal whose actual
          argument is an application of that selector's constructor is replaced by the field
          ([SMT.Smtlib2.fold_inlined_selector_reads]): [sel_i(C(t1..tn)) = t_i] in every model,
          so the problem read is equivalent and both verdicts are read.  It keeps a chain of
          definitions each passing a constructor application built from several reads of its
          formal to the next linear in size, where reading it whole doubles per level.  Set
          before the input is read ([PCSat.Solver.set_law_reader_switches], with
          [laws.read_once]) and kept for the process.  [false]: each actual copied whole into
          every read, today's reading *)
  skolem_body_variables_only : bool; [@default false]
      (** a witness of a head existential (and of a premise universal) is made a
          function of only the universals its body mentions, beside the universal
          functions a dependency set can name, instead of every universal in
          scope: a universal that occurs only in the clause's premise, a guard
          [A(w)] beside the existential, is no argument of the witness.
          Equisatisfiable in every model (inner Skolemisation), so both verdicts
          are read.  It shrinks the space of witnesses -- the four-element
          instance of a two-component contract problem goes from undecided past
          100 s to refuted in about 2 s -- but a witness the input names only
          through the dropped universal ([y := w]) is then no term, so a [sat]
          found that way can be lost.  Set before the input is read
          ([PCSat.Solver.set_law_reader_switches], with [laws.read_once]) and kept
          for the process.  [false]: every universal in scope *)
  name_quantified_premises : bool; [@default false]
      (** the input is read with every quantified premise that would multiply a clause's
          clausal form -- a written [forall] at a negative position whose negated body holds a
          conjunction mentioning an unknown -- replaced by a fresh unknown of the ordinary kind
          over its free term variables, defined by [premise => fresh] beside it
          ([PCSP.Parser.premise_definitions]), before skolemisation.  Equisatisfiable in every
          model, so both verdicts are read; the fresh unknowns are kept from every
          preprocessing elimination ([PCSP.Parser.premise_unknowns_of]), which would otherwise
          put the product back.  [false]: read as written *)
  premise_witness_disjuncts : bool; [@default false]
      (** the input is read with each positive existential of an assertion offered, as
          further disjuncts beside it, its instances at the arguments of the premises'
          applications of the defined functions its body applies
          ([SMT.Smtlib2.premise_witness_disjuncts_of]): [exists s. P(it, s) /\ ...] beside a
          premise [P(it0, hist)] gains the disjunct [P(it, hist) /\ ...].  Equivalent in every
          model (an instance implies its existential), so both verdicts are read.  Why: a
          loop postcondition whose witness is the loop invariant's own history was left,
          once the definitions were inlined, to an instantiation search of tens of seconds
          where the instance is proved at once.  [false]: read as written *)
  laws : laws; [@default Common.Util.config_default laws_of_yojson "{}"]
      (** how the [:law] premises of an SMT-LIB input are inserted and when the
          input is read (see [laws]) *)
  forced_true_release_given : bool; [@default false]
      (** with [laws.read_once] and [define_forced_true], when the kept
          assertions of the first reading name at least one unknown every
          solution makes [true], the problem of the first reading is let go
          before the input is read with them defined, instead of being held
          beside that reading: afterwards only its signature is read (to
          extend a [sat] with the [true]s).  The problem solved is the same.
          Should that reading raise, the input is read again as at first (the
          same problem up to fresh names) and solved as given.  It frees
          nothing when [check_solution] keeps the problem for the checker.
          [false]: the first problem is held until that reading returns *)
}
[@@deriving yojson]

(** Process-wide switches of the term simplifier, the evaluator and the
    qualifier normal form, independent of one another.  Each is written when
    the solver is configured and only ever turned on, so a nested solver whose
    configuration leaves one off does not switch it off under a solver running
    with it on. *)
type simplifier = {
  seq_read_range_guard : bool; [@default false]
      (** treat a sequence read whose own formula puts its index in range as a
          term the theory fixes, rather than reporting every [seq.nth] as
          interpretation-dependent; process-wide once any solver enables it *)
  abstract_oor_reads_under_binders : bool; [@default false]
      (** in a validity question with binders, replace a read of a sequence
          whose structure fixes its length, at a literal index outside it, by
          a fresh variable, guarding every other read of the same element
          sort by [ite (s' = s /\ t = k)], and a fresh sequence then seen
          only through its length by a non-negative integer; exact
          ([Ast.Evaluator.abstract_out_of_range_reads_guarded]).  Process-wide
          once on *)
  normal_forms : bool; [@default false]
      (** make the simplifier's rule outputs that a second pass would rewrite
          (an [iff]/[xor] of constants, a negated product, the constant array
          of an expanded array literal, a tester over a conditional, the
          bounds of an absolute value, a comparison turned around by grouping)
          normal forms in one pass; meaning-preserving, changes the
          simplifier's output on those shapes.  Process-wide once on, set when
          the solver is configured, so the input reader's simplification runs
          without it; see [Ast.Evaluator.simplify_normal_forms].  Off by
          default: meaning-preserving but not answer-neutral -- on a
          Rust-derived filter loop it took the CEGIS loop from 7 rounds and
          3 s to 126-148 rounds and 83-120 s *)
  skip_simplified : bool; [@default false]
      (** a conditional lifted out of an application simplifies only the nodes
          the lift built, taking its already simplified parts as they are;
          meaning-preserving, the same output wherever each part is a fixed
          point of the simplifier (always, on random formulas, together with
          [normal_forms]).  Process-wide once on, set when the solver
          is configured; see [Ast.Evaluator.simplify_skip_simplified] *)
  binders_outer_first : bool; [@default true]
      (** a quantifier block the simplifier merges from nested binders of one
          quantifier lists the outer binder's variables first, the order they
          were bound in, instead of the inner's first, which reverses the
          block on every pass and keeps a normalised formula from being a
          fixed point of normalisation.  Meaning-preserving, changes the order
          of every merged block.  Process-wide once on, set when the solver
          is configured, so the input reader's simplification runs without
          it; see [Ast.Evaluator.merge_binders_outer_first].  On by default:
          on the inputs where it acts (quantified PCSat problems, MuStrat's
          strategy constraints) no answer was lost against the inner-first
          order, and it never acts under MuVal's primal and dual solvers on
          the muCLP and integer-transition-system corpora *)
  let_inline_by_expanded_size : bool; [@default false]
      (** the simplifier inlines a [let] whose definition is small only while
          the nodes the inlining adds to the body's expanded tree stay within
          its product bound, instead of at any number of uses; a chain of
          small definitions each used more than once then stays a chain of
          [let]s rather than a tree doubling per link.  Meaning-preserving,
          changes the simplifier's output where it fires.  Process-wide once
          on, set when the solver is configured; see
          [Ast.Evaluator.inline_by_expanded_size] *)
  evaluate_sequences : bool; [@default false]
      (** evaluate sequence operators on ground values instead of asking the
          solver: a truth-table cell over a sequence literal is then decided by
          evaluation as an array cell is. Process-wide once on, see
          [Ast.Evaluator.evaluate_sequences] *)
  truth_table_seq_length_form : bool; [@default true]
      (** a truth-table cell's validity question over free sequence variables
          (a sequence parameter of a parametric example, read through
          [seq.len] and [seq.nth] of concatenations with units) is asked over
          a length and an array per sequence instead
          ([PCSatCommon.SeqLengthForm]): Z3 builds a sequence model element
          by element and does not return on a question whose countermodel
          needs a long sequence.  Exact: an answer it gives is the answer to
          the same question, and anything else is asked as before.  On by
          default, being exact.  Process-wide once on. *)
  truth_table_long_sequence_bound : int option; [@default None]
      (** [Some k] with [k > 0]: a truth-table cell's validity question that
          has a free sequence variable and an integer literal of absolute
          value at least [k], and that [truth_table_seq_length_form] has not
          decided, is not asked: the cell is left undecided, as a timed-out
          question leaves it, and nothing is recorded for the question
          ([PCSatCommon.TruthTable.asks_for_a_long_sequence]).  Z3 answers
          such a question by building the sequence element by element, and
          neither its timeout nor its resource limit bounds that in a
          long-lived process: one labeling question grew to gigabytes until
          the run was killed.  Sound as a timeout is; it costs the cells Z3
          would have decided.  [None] (and [k <= 0]): every question is asked.
          Process-wide once on. *)
  hspace_normalize_memo : bool; [@default true]
      (** keep the normal form [HypSpace.qualifiers_of] gives each qualifier
          (simplify, normalise, simplify), per domain and keyed by the
          qualifier, so that a qualifier met again in another unknown's
          hypothesis space or a later rebuild is not normalised again
          ([HypSpace.normalize_memo]).  The three steps are functions of the
          formula alone, so the qualifiers are the same.  Process-wide, only
          ever switched on.  Why: on a Rust-derived input of 23 unknowns whose
          parameters bear the same names, the first hypothesis-space update
          spent 82 s of 120 s normalising qualifiers it had normalised for
          the previous unknown.  On by default, being exact *)
}
[@@deriving yojson]

(** The known-function context admission at the SMT-LIB file entry: the
    questions it asks of a context before the problem is solved, and how it
    makes its Z3 contexts. *)
type context_admission = {
  skip_whole_questions_when_total : bool; [@default false]
      (** at the SMT-LIB file entry, when the known-function context is
          certified total, ask neither the scalar-instance refutation nor
          the projection model, the two questions of the context admission
          that assert every constraint of the problem: a total context has a
          defining model in every structure, so the first can refute only
          the problem itself (left to the solver) and the second's answer is
          not read for a total context.  On a 469-clause Rust-derived input
          the first question's conversion and assertion alone took more than
          150 s against its 1 s check budget.  Off by default *)
  full_major_every : int; [@default 1]
      (** at the SMT-LIB file entry, the forced full major collection before a
          new Z3 context is made only before every n-th context the context
          admission makes ([Z3interface.with_new_context_full_major_every]);
          1, the default, before each, as everywhere else.  The questions are
          the same; only when the collector releases dropped contexts changes,
          at most n of them waiting.  The admission makes a handful of
          contexts over the whole problem's heap: on a 469-clause Rust-derived
          input its four forced collections took 32 s of a 71 s admission
          (one run, a loaded machine), each about 8 s.  That measurement was
          taken while the admission still ran under the one-per-context rule;
          the solving entry now installs [z3.collections]
          before the admission and no collection precedes the process's first
          context, so this field only gives the admission a count of its own,
          and under [By_bytes] or [By_z3_memory] it has no effect (those
          rules ignore a stage's count). *)
}
[@@deriving yojson]

(** Before a static encoding of counted recursion, the constraints that
    mention no unknown are solved alone, as a problem with no unknown -- the
    zero-unknown verdict, the procedure that decides them when the encoding
    is off -- in a forked copy.  A refutation answers the problem [unsat] (it
    is replaced by the single constraint [false] and nothing is encoded);
    anything else (valid, undecided, a killed copy) encodes exactly as
    without it.  Sound because such a clause has one truth value under every
    interpretation of the unknowns, so a model falsifying it is one in which
    the problem has no solution.  Why: once encoded, a clause that still
    applies a recursive function under a quantifier is asked by the loop's
    validator only through questions whose [sat] answers are not models, so
    nothing refutes it there, while the zero-unknown verdict's point pin
    refutes it at a concrete point by unfolding the definitions; the plain
    validity sweep before the encoding reads the same unusable [sat]. *)
type refute_first =
  | No_refute_first  (** nothing is asked *)
  | Refute_first of {
      kill_ms : int; [@default 10000]
          (** the copy is killed after this many milliseconds of wall
              clock: the backstop for a copy that does not end by itself (a
              question Z3 does not interrupt, work outside Z3); what bounds
              each question the copy asks is [rlimit].  10 s: every
              refutation measured needs well under one second, so the kill
              decides no verdict; it bounds the cost on an input whose
              unknown-free clauses are not refuted *)
      rlimit : int option; [@default Some 100_000]
          (** a Z3 resource limit ([rlimit], Z3's count of its own search
              steps) put on every Z3 question the forked copy asks, beside
              that question's own wall-clock budget, so that where a
              question stops does not depend on the machine's load.
              Measured (Z3 5.1.0): on the two inputs where the copy refutes,
              no question it asks counts more than 3,143 (the point pin's
              [sat] that refutes is among them), so 100,000 is a 32-fold
              margin; on the inputs where nothing is refuted, the questions
              that ran out of their 0.5-1 s wall-clock budgets had counted
              0.28-3.7 million, and with this limit a copy that spent the
              whole 10 s kill on six such questions ends in under one second
              (one that asks some 260 mostly decided questions still takes
              about 9 s).  The largest count of a question decided in a copy
              that refuted nothing was 88,192, so the limit stops some
              questions that would decide; only a refutation is read, so
              that can only cost a refutation, never change one.  [None]:
              each question has only its wall-clock budget, and the copy
              only the kill *)
    }
      (** the default *)
[@@deriving yojson]

(** Before a static encoding of counted recursion, each constraint it would
    rewrite -- one that mentions no unknown and applies a counted function --
    is asked whether it is valid, with the definitions, in a forked copy; a
    constraint proved valid is dropped from the problem instead of encoded
    ([PCSP.RecFunGraph.drop_valid_encodable]).  Exact: a valid constraint
    constrains no unknown, so the problem has the same solutions, and only a
    proof is read.  Why: a counted function whose properties need no
    induction (a bit set's member count the clauses only carry, or unfold
    once) made constraints Z3 proves in a fraction of a second into graph
    unknowns whose invariant the CEGIS loop did not find in 500 s. *)
type drop_proved =
  | No_drop_proved  (** every such constraint is encoded *)
  | Drop_proved of {
      rlimit : int; [@default 2_000_000]
          (** the Z3 resource limit ([rlimit]) of the validity question.
              On the input that motivated it the four constraints asked
              were proved in 2,027-116,355 units (0.02-0.26 s), so
              2,000,000 is a 17-fold margin *)
      kill_ms : int; [@default 10000]
          (** the wall clock after which the forked copy asking one
              constraint is killed: the backstop for a question Z3 does not
              interrupt at its resource limit, read as not proved *)
      shape_proof_ms : int option; [@default None]
          (** a constraint the question above leaves unproved is asked again
              by [PCSatCommon.ShapeProof.valid_within] with this budget per
              form (the one-point rule with the constructor-tester,
              case-merge and pairing rewrites, every sequence read and
              defined function abstracted, then the premises restricted to
              those tied to the goal), and dropped when one of those forms
              is proved.  Only a proof is read, and every form implies the
              constraint, so the problem keeps its solutions.  Why: the
              layout obligations of [univariant_sat.smt2] are instances of
              their premises that Z3 does not find (no ground term to
              match), and graph unknowns for them were not found by the
              loop; the shape forms are proved in under a second.  [None]
              (the default): not asked *)
      weaken_refused_ms : int option; [@default Some 1000]
          (** a constraint the questions above leave unproved is asked once
              more, within this budget, as the weakening of its negation by
              [PCSP.RecFunGraph.abstracted_weakening]: the conjuncts
              [Z3interface.may_not_return] refuses (a premise quantified over
              sequences, typically a callee's lemma) are dropped, every
              application of a counted function outside a binder becomes a
              fresh variable, and a conjunct still applying one is dropped.
              Only an [unsat] is read, and the weakening is implied by the
              negation, so it proves the constraint valid and the problem
              keeps its solutions; a constraint left with nothing costs
              nothing.  Why: a lemma used at the constraint's own sequence,
              once instantiated there ([PCSP.RecFunGraph.binder_instances]),
              decides a bit set's type-invariant obligation without its
              quantified statement or the definition, while Z3 asked the
              whole question (8 s, unproved at the kill) or the rest with the
              definition in context (2 s) did not answer it.  The budget: the
              proof that motivated it took 0.25 s, and on inputs where the
              question proves nothing each one runs to the budget (5-6 per
              run), so 1000 ms keeps a fourfold margin at half the cost of
              2000.  [None]: not asked *)
      name_bv_to_int : bool; [@default false]
          (** each question above (the native one and the weakened one) is
              asked with every [bv_to_int_n] application named by a function
              symbol of its own and that symbol's definition as the inverse
              of [int_to_bv_n] made a premise
              ([Ast.QuestionRewrites.name_bv_to_int], which proves that the
              rewritten question is valid exactly when the constraint is).
              Why: Z3 splits [bv2nat (bvor w c)] into extracts before the
              round trip through [int2bv] collapses, and a bit read back from
              a word sequence updated by [bvor] then stalls it; behind the
              named symbol the same question was proved in 6-8 s.  [false]
              (the default): asked as it is *)
      free_int_singletons : bool; [@default false]
          (** each question above is first rewritten by
              [Ast.QuestionRewrites.pin_free_int_singletons]: a free integer
              variable that the constant bounds among the question's
              literals confine to one value is replaced by that value, as a
              bound one already is (valid exactly when the constraint is).
              [false] (the default): bound variables only *)
      int_universal_read_instances_ms : int option; [@default None]
          (** a constraint the questions above leave unproved is asked once
              more by a forked copy, within this budget (and [rlimit]), as
              the native question with each integer universal among the
              conjuncts of its negation that reads a sequence at its
              variable replaced by its instances at the positions the
              question's ground sequence reads and the predecessors of its
              function applications' integer arguments give
              ([Ast.QuestionRewrites.int_universals_at_positions]), the
              universal itself dropped.  A weakening of the negation, so
              only an [unsat] is read, as a proof; the problem keeps its
              solutions.  The native form, not the weakened one: the
              weakened question abstracts the counted applications whose
              arguments give the predecessors.  Why: a membership question
              after an insertion into an empty set, refuted by the set's
              zero-word premises at word 0, was not answered by Z3 at 30 s
              with the premises kept and was answered in under a second with
              those instances in their place.  Asked only when the rewrite
              offers an instance.
              [None] (the default): not asked *)
    }
      (** the default *)
[@@deriving yojson]

(** A static encoding applied to the problem the preprocessor works on,
    encoding only its clauses that mention no unknown THERE
    ([PCSP.RecFunGraph.encode_clauses ~unknown_free_only:true]): a clause
    whose unknowns predicate elimination removed is encoded, one that still
    has an unknown is not.  The read-time encoding is then not applied on any
    path, so no constraint is encoded twice; every reading of the input (the
    forced-true one and the probes') reaches the loop through the
    preprocessor, so the decision is the same on every path.  Contract and
    equisatisfiability: [encode_clauses]; the problem preprocessing recorded
    its eliminations against is not changed, so completing a solution with
    the eliminated predicates is as without the encoding. *)
type graph_after = {
  candidates : bool; [@default false]
      (** give every graph unknown introduced the atoms [r_i = f(a_i, j)]
          stating its intended solution, the graph of the calls it replaces,
          as declared candidate atoms (qualifiers of its hypothesis space and
          the Houdini pre-pass's starting conjunction), and keep the
          functions they apply in the problem's environment.  The graph
          solves the encoding's base and step clauses and turns its goal
          back into the original constraint, so an encoded constraint is
          reachable from what the unencoded one offers.  Hints only: no
          constraint changes.  [false]: the graph unknown starts from the
          hypothesis space alone and the function leaves the environment
          when nothing applies it *)
  dynamic : bool; [@default false]
      (** also encode, after preprocessing, a clause that applies a counted
          function when validation leaves it undecided (the solver neither
          confirms nor refutes a candidate on it), and solve again
          ([PCSatCommon.RecFunDynamic] has the contract), as [Dynamic_only]
          does, on top of the static encoding *)
  refute_first : refute_first;
      [@default Common.Util.config_default refute_first_of_yojson {|["Refute_first", {}]|}]
      (** asked when the encoding introduces a graph unknown *)
  drop_proved : drop_proved;
      [@default Common.Util.config_default drop_proved_of_yojson {|["Drop_proved", {}]|}]
      (** asked before the encoding *)
}
[@@deriving yojson]

(** Where the encoding of counted recursion is applied. *)
type graph_placement =
  | As_read of {
      unknown_free_only : bool; [@default false]
          (** encode only the constraints that mention no unknown, keeping
              every other constraint as it is (still equisatisfiable: each
              constraint is encoded on its own).  A function applied only
              beside unknowns that predicate elimination removes is then
              left to the validity question that remains after elimination,
              which may need no induction, instead of becoming a recursive
              unknown that stops elimination.  [false]: every constraint
              with a counted application is encoded *)
      every_reading : bool; [@default false]
          (** encode every problem a re-reading of the input gives (the
              forced-true reading, and the readings the least-definition,
              true-precondition and lower-bound probes solve) as the problem
              read first is encoded, so that the encoding is in force on
              every path whichever reading is solved.  Contract: on each
              path the problem solved is [PCSP.RecFunGraph.encode] of that
              path's reading with this configuration's arguments, and every
              verdict stays sound (the encoding is equisatisfiable).
              [false]: a re-read problem is solved as read, so an unknown
              forced [true] by an unrelated clause switches the encoding
              off *)
      candidates : bool; [@default false]
          (** as [graph_after.candidates] *)
    }
      (** the problem as read is encoded ([PCSP.RecFunGraph.encode]) *)
  | After_preprocessing of graph_after
      (** the encoding of [graph_after] applied to the problem the
          preprocessor hands the CEGIS loop, after its last pass, where no
          pass sees the graph unknowns (a 64-bit word argument of a graph
          unknown then gets no range invariant) *)
  | After_elimination of graph_after
      (** the encoding of [graph_after] applied right after predicate
          elimination (the preprocessor's [post_elim] hook): the clauses it
          encodes are the same kind (mention no unknown once elimination has
          run), and the graph unknowns then go through the passes after
          elimination -- argument reduction and sharing, and the word ranges
          put around the solver call -- as read-time graph unknowns do.
          Equisatisfiable for the same reason; an added unknown is reduced
          like one the elimination added.  With the preprocessor disabled the
          hook is not reached and nothing is encoded.  The default *)
  | Dynamic_only
      (** no static encoding: after preprocessing, a clause that applies a
          counted function is encoded when validation leaves it undecided
          (the solver neither confirms nor refutes a candidate on it), and
          the problem solved again ([PCSatCommon.RecFunDynamic] has the
          contract).  Only clauses of the problem the preprocessor handed on
          are encoded, each at most once, so the restarts are finitely many.
          The examples of clauses still present are kept (the solver
          context's version reuse), those derived from an encoded clause are
          dropped, and the function environment is kept whole.  The
          read-time encoding is off *)
[@@deriving yojson]

(** Counted recursion as graph unknowns: each application of a counted
    recursive function (a [define-fun-rec] whose body is
    [ite (k <= c) base step] with one recursive call at [k - 1], every other
    argument passed on) is replaced by an ordinary unknown for the graph of
    the applications at one counter term, with a base and a step clause
    ([PCSP.RecFunGraph.encode]; equisatisfiable), and the definitions the
    result no longer applies leave the problem's function environment.  A
    property of such a function stated with no unknown leaves the induction
    that proves it to the zero-unknown validity check, which no SMT solver
    does; as an unknown it is an invariant the synthesiser looks for, as in
    the loop spelling of the same function. *)
type graph =
  | Off  (** the problem as given *)
  | Graph of {
      placement : graph_placement;
          [@default
            Common.Util.config_default graph_placement_of_yojson
              {|["After_elimination", {}]|}]
    }
      (** the default *)
[@@deriving yojson]

(** Turning an eligible ordinary unknown (it occurs only in its defining
    clauses, which mention no other unknown, and as a premise elsewhere; the
    last argument is the result) back into the recursive function its
    defining clauses compute, when the clauses' guards are proved mutually
    exclusive and exhaustive and the function is proved total (a
    lexicographic structural or integer measure decreasing at every
    recursive call), and adding that function to the function environment
    and its applications to the vocabulary of the template and the Houdini
    pre-pass ([PCSatCommon.RecFunReconstruct.reconstruct]).  The unknown
    stays an unknown.  Only enlarges the hypothesis space; a predicate whose
    checks are not all proved is left as it is. *)
type reconstruction =
  | No_reconstruction
  | Reconstruct of {
      result_guards : bool; [@default true]
          (** also reconstruct an unknown whose defining clauses test the
              RESULT of a recursive call in their guard (a refinement guard
              [len(t, n) /\ n >= 0 => len(c :: t, n + 1)], or a case split on
              a Boolean call [mem(e, t, true) => mem(e, c :: t, true)]): each
              such conjunct is kept in the branch's guard with the call's
              value in place of its result variable, so the function
              evaluates the call before testing it
              ([RecFunReconstruct.reconstruct ~result_guards:true]).  The
              checks are those of the plain case: the guards' exclusivity and
              exhaustiveness are asked with the function read as an
              uninterpreted symbol (valid for every interpretation, hence for
              the function), and totality by a measure decreasing at every
              call under the call-free part of its guard, which holds
              wherever the call is evaluated.  Guards not proved exhaustive
              (a refinement guard such as [n >= 0] is not exhaustive for an
              arbitrary function) give the default-completed function,
              vocabulary only.  Only enlarges the hypothesis space.
              [false]: such an unknown is refused *)
      compositions : bool; [@default false]
          (** also reconstruct an unknown whose defining clauses apply
              another unknown that has itself been reconstructed with
              exhaustive guards ([height] through [nmax], [rev] through
              [append]): such an atom [q(a, w)] is read as the call
              [w = g(a)] of [q]'s function [g], the unknowns being tried
              again in passes until none is added, and an unknown applied in
              the body of a clause whose head is another unknown is no
              longer refused for that.  Every function so obtained passes
              the same checks (exclusive guards, totality, every applied
              function total); one whose eligibility needed either
              relaxation is vocabulary only, never put in the unknown's
              place ([RecFunReconstruct.reconstruct ~compositions:true]).
              Only enlarges the hypothesis space.  [false]: such an unknown
              is refused *)
      reuse_equal_functions : bool; [@default true]
          (** a reconstructed function proved equal in every model to a
              total function the environment already has
              ([RecFunReconstruct.equal_existing]: both bodies one unfolding
              apart with the calls read as one uninterpreted symbol, so the
              question needs no induction) is not added under a new name;
              the existing function is the unknown's reconstruction
              (replacement, the bounded reconstructed-function qualifiers).
              Exact: every term or qualifier the new name would give has an
              equivalent one over the existing function, so the hypothesis
              space is the same up to equivalence; it loses the duplicates,
              whose cells comparing the two functions at a parametric
              example need induction and leave a truth-table question that
              never returns.  It changes the search (fewer qualifiers and
              terms); on the inputs where it acts it removed a truth-table
              cell that did not return and lost no answer.  [false]: every
              reconstruction gets a name of its own *)
      replace_predicates : bool; [@default false]
          (** also replace each reconstructed unknown [rho(a, b)] by
              [b = f(a)] and drop its defining clauses (equisatisfiable for a
              total function: the unknown's least solution is the function's
              graph, and it occurs elsewhere only as a premise).  [false]:
              the unknown stays *)
      quals : int; [@default 16]
          (** at most this many qualifiers per unknown applying a
              reconstructed function at the terms its parameters reach (as
              [rec_fun_app_quals] states, with also [x = f(t)] for a Boolean
              parameter [x] and a Bool-valued [f]), in the template and in
              the Houdini pre-pass alike *)
    }
      (** the default *)
[@@deriving yojson]

(** Lemmas about the recursive functions shown total (an input
    [define-fun-rec] or a reconstructed one), recorded as the function's
    property, which every query applying the function conjoins at each
    application.  Each lemma is proved valid by induction over the measure
    that showed totality; nothing unproved is recorded. *)
type lemmas = {
  built_in : bool; [@default true]
      (** prove the jointly inductive subset of candidate invariants from
          the function's signature (an integer result's sign and its order
          against integer arguments and sequence lengths, a sequence
          result's length, a Boolean result's implications with argument
          testers).  [false]: no built-in lemma *)
  user : bool; [@default true]
      (** try the lemmas the input states about its recursive functions
          ([(define-fun L (ys) Bool phi)] with [(set-info :lemma L)], or the
          older [(set-info f (forall ys. phi))]) as candidate invariants of
          each function shown total that they apply, together with the
          built-in candidates whether or not [built_in] is on, and record
          the jointly inductive subset.  A user lemma is a claim to be
          proved: one not proved is ignored (reported in the trace), never
          assumed.  No effect on an input stating no lemma.  [false]: user
          lemmas are read and ignored *)
}
[@@deriving yojson]

(** Where the known-function certificate's residual question is asked
    ([Z3interface.residual_contexts]).  Only a proof of the residual is read,
    so every choice gives a sound certificate; what can differ is which
    residuals are decided within the question's 1 s, and the time spent
    making contexts and collecting dropped ones. *)
type residual_contexts =
  | Residual_fresh  (** a fresh context per question; the default *)
  | Residual_clean_pool
      (** a clean pooled context, reset between questions
          ([Z3interface.with_clean_reset_pool]); the residual is asked with no
          function environment and never pushes, the two conditions under
          which a reset context decided less than a fresh one *)
  | Residual_full_major_every of int
      (** a fresh context per question, with the forced full major
          collection before every n-th new context only
          ([Z3interface.with_new_context_full_major_every]) *)
[@@deriving yojson]

(** How defined (recursive) functions reach the solver's questions and the
    hypothesis space.  Each switch is process-wide once on: a later
    configuration that leaves it off does not switch it off. *)
type definitions = {
  eval_ground_qualifiers : bool; [@default false]
      (** a truth-table cell whose qualifier applies a defined function is
          first rewritten by unfolding the definitions along their guards
          ([Evaluator.unfold_rec_apps]); the rewritten qualifier, which
          applies no defined function, replaces the original when the
          unfolding completes, and the cell is evaluated as before otherwise
          ([PCSatCommon.TruthTable.eval_recursive_qualifiers_ground]).
          Exact: each step is an instance of the definition's equation.  At
          a ground example the value is then computed by evaluation instead
          of being asked of Z3 as a quantified question under a budget; at a
          parametric example a guard over a parameter stops the unfolding *)
  skip_induction_cells : bool; [@default false]
      (** a parametric truth-table cell whose qualifier applies a defined
          function, and whose unfolding along the definitions' guards stops
          at a guard reading one of the example's parameters (the value
          needs induction), is left undecided without asking the solver, as
          a timed-out question leaves it
          ([PCSatCommon.TruthTable.skip_induction_cells]).  Sound as a
          timeout is; it can leave undecided a cell the solver would have
          decided.  Independent of [eval_ground_qualifiers] *)
  prune_unreached : bool; [@default false]
      (** the problem the CEGIS loop starts from (after preprocessing, and in
          each nested solve) keeps in its own function environment
          ([Params.fenv]) only the definitions its clauses reach and the size
          functions ([PCSP.Problem.prune_unreached_definitions]).  The
          template hypothesis space applies every other function of that
          environment to the parameters' terms, so an unused recursive
          definition became qualifiers whose truth at a parametric example Z3
          had to decide by unfolding the recursion, past the query's own
          timeout: a linear loop answered in 2 s gave no answer in 60 s with
          one unused [define-fun-rec] beside it.  The clauses are unchanged;
          the hypothesis space loses the applications of definitions nothing
          applies.  The process-global environment is untouched; this one
          switch is per configuration, not process-wide.  Dropping
          definitions is not a general full-context equivalence: unused
          recursive equations can be inconsistent or constrain shared
          symbols.  Preservation requires an extension satisfying the
          omitted equations; the reachability walk does not check that
          condition. *)
  declare_reached_only : bool; [@default false]
      (** declare to Z3 only the defined functions a query reaches
          (directly, or through another reached function's definition or
          recorded property), in the pooled entry points of [Z3interface]
          and in the synthesis phase's long-lived instances, instead of every
          function of the problem's environment
          ([Z3interface.fenv_for_query], [Z3interface.declare_reached]).  A
          definition registered with a context changes Z3's answers there
          even when nothing applies it: a linear loop answered in 2 s
          stalled in synthesis with one unused recursive definition beside
          it.  Reached functions are declared and defined as before, but
          absence from converted formulas does not make an omitted defining
          equation irrelevant.  Full-context equivalence requires a
          model-extension condition that this switch does not check *)
  residual_contexts : residual_contexts; [@default Residual_fresh]
      (** where the known-function certificate asks its residual question
          (the question with the model's values substituted and the
          definitions unfolded, read only when Z3 proves it valid); see
          [Z3interface.set_known_function_residual_contexts] and
          [residual_contexts].  Process-wide once a configuration sets
          something other than the default *)
  open_residual_rlimit : int option; [@default None]
      (** a second certificate for a native [sat] to a question applying a
          known (defined) function, asked when the residual (the question
          with the model's values substituted and the definitions unfolded)
          is not valid: accept it when the residual is quantifier-free, has
          no free symbol but the model's element constants, and is
          satisfiable with those constants pairwise distinct, under a Z3
          resource limit of this many units (a 1 s wall clock kept only as a
          kill); [null] (the default) leaves it off.  The residual is then
          not valid typically because it reads a term the theory leaves open
          ([hd nil] from a candidate reading [hd (tl x)] at a one-element
          list), and the [sat] is then certified in some model of the theory
          with the definitions rather than in the background part of the
          native model; see [Z3interface.open_residual_is_satisfiable] *)
}
[@@deriving yojson]

(** Everything PCSat does with the input's recursive functions: encoding
    counted recursion as graph unknowns, reconstructing functions from
    unknowns, proving lemmas about them, and how their definitions reach the
    solver. *)
type recursive_functions = {
  graph : graph; [@default Common.Util.config_default graph_of_yojson {|["Graph", {}]|}]
  guarded_counter : bool; [@default false]
      (** the encoding of counted recursion also accepts a body guarded by a
          lower bound on its counter, [ite (k >= c') (ite (k <= c) base step)
          base] with [c' <= c + 1], as the counted body
          [ite (k <= c) base step] it equals
          ([PCSP.RecFunGraph.guarded_body]); a front end stating a
          termination measure emits that guard.  Passed to every entry
          point of the encoding in the run, so all of them recognise the same
          definitions.  [false]: such a function is not counted, so a property of it stated
          with no unknown is left to the zero-unknown validity check *)
  reconstruction : reconstruction;
      [@default
        Common.Util.config_default reconstruction_of_yojson {|["Reconstruct", {}]|}]
  names_apart : bool; [@default false]
      (** the pass that reconstructs functions and proves their lemmas (run
          when reconstruction or either kind of lemma is on) draws its fresh
          term-variable names from a counter of its own
          ([RecFunReconstruct.reconstruct ~names_apart:true]), so the
          process-global counter is where it was before the pass and the
          rest of the run names what it builds as it would without the pass.
          Exact: the pass's result is the same up to the names it draws.
          [false]: the pass draws from the global counter *)
  lemmas : lemmas; [@default Common.Util.config_default lemmas_of_yojson "{}"]
  refuse_seq_quantified_questions : bool; [@default true]
      (** the pass that reconstructs functions and proves their lemmas does
          not ask a validity question that binds a sequence (or another sort
          Z3 has no complete quantifier support for) under a quantifier
          ([Z3interface.may_not_return]); the question counts as not proved
          ([RecFunReconstruct.refuse_seq_quantified]).
          Contract: sound, not exact.  A refused question only drops a
          candidate lemma or reconstruction, never adds one, so every answer
          the run gives is one it could give with the question asked; it can
          drop a lemma Z3 would have proved, and so lose an answer that lemma
          carried.
          Why on: such a question can run to the pass's 5 s kill while Z3's
          resource counter stays far below its limit, so the resource limit
          does not bound it (six lemma questions on a Thrust iterator input,
          each undecided at the kill with 0.5-0.75 M of 4 M units spent, took
          that input from under a second to 36 s).  Over the Thrust inputs
          and every other sequence-sorted constraint problem of the corpora,
          three runs a side at 120 s, the refusal cost no answer on any file
          it acted on.
          [false]: every question is asked *)
  definitions : definitions;
      [@default Common.Util.config_default definitions_of_yojson "{}"]
}
[@@deriving yojson]
(** How a probe is run: not at all, before what follows it, or in a forked
    copy of the process raced against what follows it
    ([PCSatCommon.ParallelRace]): the first answer wins, the copy's being
    only the verdict the probe reads, which is sound on its own, so each
    answer the process can give is one the sequential order could give.
    When the process cannot fork (it has spawned a domain) a raced probe
    runs sequentially. *)
type probe_mode = Off | Sequential | Raced [@@deriving yojson]

(** whether a probe in [mode] is run at all *)
let probe_runs = function Off -> false | Sequential | Raced -> true

(** whether a probe in [mode] is raced in a forked copy *)
let probe_raced = function Raced -> true | Off | Sequential -> false

(** the mode of a probe that is run when [on] and raced when [raced] too:
    [Off] when not [on], whatever [raced] is *)
let probe_mode_of ~on ~raced =
  if not on then Off else if raced then Raced else Sequential

(** The true-precondition probe ([PCSatCommon.TruePrecondition]): with an
    [.smt2] input file, first read the file again with each selected unknown
    (Boolean, of the ordinary kind) defined as [true] and solve that; a [sat]
    of it, extended with the [true]s, is the answer, and any other outcome --
    [unsat] included -- is discarded and the problem is solved as given.
    Only [sat] is read, and it is sound: a solution of the substituted
    problem together with [p := true] is a solution of the original.  The
    substitution is made before the reader's skolemisation, which an unknown
    under an existential triggers.  The probe tries something only when
    [names] is non-empty or [witness_causing] holds. *)
type true_precondition_probe = {
  mode : probe_mode; [@default Raced]
      (** [Raced] (the default): concurrently with the problem solved as
          given (and the lower-bound probe before it).  A cooperative budget
          does not bound a phase that does not return, so the sequential
          probe can take more than its budget away from the problem as given
          -- measured, a probe whose zero-unknown check ran 125 s past a 60 s
          budget -- and the race removes that cost at the price of a second
          process *)
  names : string list; [@default []]
      (** the unknowns selected by name *)
  witness_causing : bool; [@default true]
      (** beside [names], select the unknowns that occur beneath a
          quantifier existential in effect (a written [exists] at a positive
          position, a written [forall] at a negative one) -- exactly the
          unknowns that make the reader skolemise a quantifier into a
          functional predicate ([PCSP.Parser.witness_causing_unknowns]).
          The selection decides only what is tried; the answer read is still
          only a [sat] of the substituted problem.  [false]: only the named
          unknowns *)
  skip_forced_only : bool; [@default true]
      (** give up at once, answering nothing, when every unknown the probe
          would define as [true] is one the forced-true reading
          ([reader.define_forced_true]) already defined as [true] -- which is
          the case on an input with no witness-causing unknown and a forced
          one, since the probe re-reads the input with the forced unknowns
          defined too.  Its problem is then the problem the process solves
          as given, so it could answer only what that solve answers; raced,
          it was a second process solving the same problem (without the
          Houdini pre-pass, which a solve under a deadline skips) beside the
          first.  On the Thrust corpus that was 125 of 172 inputs and 83% of
          the probe copies' time, and on the five such inputs the copy used
          to answer first the process answered alone in 10 of 10 runs, no
          slower.  [false]: the probe solves the re-read problem whatever it
          defines *)
  budget_ms : int; [@default 60000]
      (** the probe's cooperative deadline (strict: read at the loop's phase
          boundaries and by the synthesizer), which does not bound a phase
          that does not return; the problem solved under it also skips the
          Houdini pre-pass, as every solve under a deadline does *)
}
[@@deriving yojson]

(** The lower-bound probe: with an [.smt2] input file, after the
    true-precondition probe (when that is on) read the file again with each
    selected unknown (Boolean, of the ordinary kind) replaced by [true] where
    it is demanded and by a lower bound derived from the input's own
    constraints where it is assumed ([PCSP.Parser.lower_bound_relax]), and
    solve that; an [unsat] of it is the answer, and any other outcome is
    discarded and the problem solved as given.  Only [unsat] is read, and it
    is sound: the read problem is a relaxation, every solution of the input
    in a model restricting to one of it in that model.  The probe tries
    something only when [names] is non-empty or [witness_causing] holds. *)
type lower_bound_probe = {
  mode : probe_mode; [@default Sequential]
      (** [Raced]: concurrently with the problem solved as given; the copy
          answers only with the probe's [unsat].  The probe's budget does not
          bound its preprocessing, so sequentially its whole time is added to
          every input it does not answer -- every satisfiable one.  The
          default: [Sequential] *)
  names : string list; [@default []]
      (** the unknowns selected by name *)
  witness_causing : bool; [@default true]
      (** beside [names], select the unknowns that occur beneath a
          quantifier existential in effect, as the true-precondition probe's
          [witness_causing] does.  [false]: only the named ones *)
  skip_unrelaxable : bool; [@default true]
      (** the probe is not made, and its reading of the input is not taken,
          when an earlier reading of the same file under the same reader
          switches, with the same unknowns defined as [true] (the forced-true
          reading, [reader.define_forced_true]), shows that the relaxation
          would relax nothing: no named unknown and no witness-causing
          unknown that is Boolean-valued and of the ordinary kind
          ([PCSP.Parser.relaxable_known]).  The probe reading then builds the
          same assertions, its relaxation returns no relaxed unknown, and the
          probe discards it unread, so skipping it changes no answer and no
          question; it removes a whole reading of the input.  With no such
          earlier reading, the probe reads as without this.  It also makes
          every reading record what that check reads
          ([PCSP.Parser.record_relaxable]), whatever [mode] is.  [false]: the
          probe always reads *)
  rounds : int; [@default 2]
      (** how many rounds the lower bounds are iterated from [false]; each
          round lets a bound use the bounds of the unknowns a demand of it
          assumes *)
  budget_ms : int; [@default 60000]
      (** the probe's cooperative deadline, as the true-precondition
          probe's *)
  max_input_bytes : int; [@default 4_000_000]
      (** the probe is not tried on an input file larger than this many
          bytes.  It reads the whole file a second time, and its relaxation
          walks each clause with a side condition per disjunction it passes,
          which grows with the square of a clause's length: on a 25 MB input
          the second reading and the walk had not finished after 220 s and
          then exhausted 6 GB, where the inputs the probe answers are under
          250 KB and the largest of the others measured under 2.5 MB.
          Skipping it changes no answer, only whether an [unsat] is found
          this way. *)
  early_stages_only : bool; [@default false]
      (** while the probe solves, the zero-unknown verdict stops after its
          early stages -- the quick sweep, the early pins and the early exact
          forms -- and answers undecided where they decide nothing
          ([PCSatCommon.NoUnknownLadder.early_only]); the sequence
          instantiation, which can only prove, is not run either.  Every
          [unsat] the probe gives with it is one it gives without; one that
          only the whole-clause questions, the rewritten questions or the late
          pins would find is lost.  On satisfiable inputs those stages are
          where the probe spent its time: the early sequence instantiation
          alone held the probe for 99 s of a 120 s run, and the stages after
          the early ones about 200 s of a 300 s one, while every refutation the probe
          gave on the corpus measured came from the preprocessing, the quick
          sweep or an early pin.  [false]: the whole ladder *)
}
[@@deriving yojson]

(** The witness-seed probe: first solve the problem with every functional
    witness of a guarded body universal [forall q. lo <= q < hi => ...]
    defined as the last index, [w(x, r) := r = hi - 1]
    ([PCSatCommon.WitnessSeed]), under [budget_ms]; a [sat] of it, extended
    with the definitions, is the answer, and any other outcome is discarded
    and the problem solved as given.  Only [sat] is read, and it is sound:
    each definition is a total, single-valued function, so it is one choice
    of the witness. *)
type witness_seed_probe = {
  mode : probe_mode; [@default Sequential]
      (** [Raced]: the probe, seeds included, concurrently with everything
          after it (the true-precondition and lower-bound probes and the
          problem as given); the copy answers only with the probe's [sat],
          extended with the seeds.  The budget does not bound the probe's
          preprocessing or its zero-unknown check, so sequentially a probe
          that runs long delays every input it does not answer by all of its
          time.  The default: [Sequential] *)
  after_preprocessing : bool; [@default false]
      (** with [Sequential]: the seeds are read off the problem as given, as
          before, but the seeded problem is not preprocessed on its own.
          Instead the problem as given is preprocessed once, and the seeds of
          the witnesses that survive it with their argument sorts unchanged
          are substituted into the preprocessed clauses (only the clauses
          applying them are rebuilt); that problem is solved under
          [budget_ms], a [sat] of it extended with the seeds is the answer of
          the preprocessed problem, and any other outcome goes on with the
          preprocessed problem itself.  Sound for the same reason as the
          probe: a seed is one choice of a total, single-valued witness of
          the preprocessed problem, whose solutions extend to the input's.
          Not the same problem as the sequential probe's: preprocessing the
          seeded problem may simplify further.  Why: on a Thrust coroutine
          input the seeding changed 1 of 469 constraints and the probe spent
          minutes preprocessing the other 468 before the problem as given was
          preprocessed again.  [false]: the sequential probe preprocesses the
          seeded problem *)
  filter_disjuncts : bool; [@default true]
      (** the bounds are read converting only the disjuncts of a clause's
          pure part that mention the witness's last argument, rather than the
          whole pure part once per witness atom
          ([PCSatCommon.WitnessSeed.disjuncts_mentioning]); the seeds are the
          same.  Why: on Rust-derived inputs with large pure parts the
          whole-part conversion took 87 s to more than 300 s before any
          solving began *)
  budget_ms : int; [@default 60000]
      (** the probe's cooperative deadline, as the true-precondition
          probe's, for the seeded solve in either form *)
}
[@@deriving yojson]

(** The least-definition probe: with an [.smt2] input file, before the
    witness-seed probe, read the file again with every unknown that makes
    the reader skolemise a quantifier ([PCSP.Parser.witness_causing_unknowns])
    defined, at every occurrence, as the lower bound the input's own
    constraints give it after [rounds] rounds
    ([PCSP.Parser.lower_bound_define]), and solve that under [budget_ms]; a
    [sat] of it, extended with the definitions, is the answer, and any other
    outcome is discarded and the problem solved as given.  Only [sat] is
    read, and it is sound: the definitions are one choice of those unknowns.
    The guess suits a closure's precondition and postcondition left to
    inference and assumed by a library loop beneath a universal: the least
    solution of the postcondition is what the closure's body gives, while a
    skolemised witness of the universal would have to name an index at which
    the closure accepted, which no term over the clause's variables is. *)
type least_definition_probe = {
  mode : probe_mode; [@default Raced]
      (** [Raced] (the default): concurrently with everything after it (the
          witness-seed, true-precondition and lower-bound probes and the
          problem as given).  The probe never answers an unsatisfiable input,
          so sequentially its whole time -- a full preprocessing and
          zero-unknown check of the defined problem, under a cooperative
          budget that does not bound a phase that does not return -- is added
          to every such input *)
  rounds : int; [@default 3]
      (** the rounds of the lower bounds; each round lets a bound use the
          bounds of the unknowns a demand of it assumes, so a postcondition
          established from a fact through k intermediate unknowns needs
          k + 1.  A Thrust closure's body reaches its postcondition through
          two (the body's entry and its result), and a round more than needed
          adds the disjuncts of the occurrences beneath a head universal,
          quantified, which the definition drops again but which cost
          reading time to build *)
  budget_ms : int; [@default 60000]
      (** the probe's cooperative deadline, as the true-precondition
          probe's *)
}
[@@deriving yojson]

(** The upper-bound definition probe: with an [.smt2] input file, before the
    least-definition probe, read the file again with every witness-causing
    unknown ([PCSP.Parser.witness_causing_unknowns]) defined, at every
    occurrence, by one candidate of [PCSP.Parser.upper_bound_candidates] --
    the upper bound the input's constraints give it where it is assumed, or
    that bound with one parameter or one field of a parameter made universal
    -- and solve that under [budget_ms]; the candidates are tried in turn,
    and the first [sat], extended with the definitions, is the answer.  Only
    [sat] is read, and it is sound: a definition is one choice of the
    unknown.  The guess suits a closure's precondition left to inference: the
    closure's body bounds it from above by what the body needs, and a
    precondition on a mutable borrow is that bound with the borrow's final
    value made universal, since its callers establish it for every prophecy.
    On by default and sequential: on the Rust-derived inputs it answers a
    closure precondition no other route answered, and with
    [skip_no_targets] it costs nothing on an input with no target. *)
type upper_bound_definition_probe = {
  mode : probe_mode; [@default Sequential]
      (** [Raced]: concurrently with everything after it; the copy answers
          only with the probe's [sat].  [Sequential] is the default: raced,
          the copy shares the machine with the process's own lower-bound
          probe on exactly the inputs it answers, and on the closure input it
          was made for it answered none of four runs within 120 s where the
          sequential probe answered all *)
  skip_no_targets : bool; [@default true]
      (** the probe is not made, and its reading of the input is not taken,
          when an earlier reading of the same file under the same reader
          switches, with the same unknowns defined as [true] (the forced-true
          reading), shows that the input has no witness-causing unknown that
          is Boolean-valued and of the ordinary kind
          ([PCSP.Parser.relaxable_known], the record the lower-bound probe's
          [skip_unrelaxable] reads too).  Those are exactly the unknowns the
          probe's candidates are built for
          ([PCSP.Parser.upper_bound_definitions] starts from
          [define_true_targets] of the witness-causing unknowns), so the
          reading would define nothing and the probe would discard it
          unread: skipping it changes no answer and no question and removes
          a whole reading of the input from every input it applies to.  With
          no such earlier reading the probe reads as without this.  [false]:
          the probe always reads *)
  skip_refutations : bool; [@default true]
      (** the preprocessing of each candidate's solve runs none of the costly
          stages that can only refute ([Preprocessing.Preprocessor.refutation_unread]:
          the refutation by unfolding, the finite instantiation, the
          universal-function instances; the cheap unknown-free sweeps still
          run, because a candidate they refute would otherwise reach the
          zero-unknown verdict, which found the same refutation 5-8 s later
          over five candidates of one input): the probe reads only [sat], and
          each such stage either leaves the problem as it is or replaces it by
          [false], so no [sat] the probe can reach is lost.  Inside the
          probe's bounded solve these stages run in sequence, not raced: on a Rust-derived input the refutation by
          unfolding took 51 s of a 118 s preprocessing, under a 60 s budget,
          and refuted nothing.  The cost is on a candidate whose problem such
          a stage would refute early: its solve then runs to the budget.
          [false]: every stage runs, as before the field existed *)
  max_input_bytes : int; [@default 4_000_000]
      (** the probe is not tried on an input file larger than this many
          bytes, as the lower-bound probe's [max_input_bytes] bounds that
          probe.  The probe reads the whole file again for each candidate it
          tries, and on a 4.7 MB input whose witness-causing unknowns the
          earlier reading did not rule out, that reading alone had not
          finished after 566 s, while the inputs the probe answers are under
          250 KB.  Skipping it changes no answer the probe does not give,
          only whether a [sat] is found this way *)
  budget_ms : int; [@default 60000]
      (** the probe's cooperative deadline, as the true-precondition
          probe's, for each candidate's solve *)
  whole_budget_ms : int option; [@default None]
      (** [Some ms]: one strict deadline, [ms] from the start of the probe's
          first reading, over the whole probe -- every candidate's reading of
          the input and its solve.  It is the same cooperative deadline as
          [budget_ms] ([PCSatCommon.SolveDeadline.within ~strict_budget:true]),
          set around the loop over candidates, so each candidate's solve is
          bounded by the earlier of its own [budget_ms] and what is left of
          [ms], and it is read where that deadline is read (with
          [deadline_in_preprocessing], [deadline_at_stages] and the
          zero-unknown ladder's [reads_strict_deadline] also there) and at
          two points of this probe's own: no further candidate is read once
          it has passed, and a candidate filter's validity question is not
          asked once it has passed (an unasked question drops no candidate,
          as an undecided one does).  Only the probe's [sat] can be lost.
          Why a time bound at all: the probe's cost is the number of
          candidates times a reading and a solve, the count is a property of
          the input that is known only after the first reading, and no
          answer-shaped test decides before a solve whether a candidate's
          problem is satisfiable; so the bound is on time, and it is put on
          the deadline already there rather than on a timer of its own.
          [None] (the default): no bound over the candidates, each bounded by
          [budget_ms] alone, as before the field existed *)
  filter_memo : bool; [@default true]
      (** the candidate filter's validity questions are asked once per
          probe and their answers kept for the probe's later readings: each
          candidate is tried on a reading of its own, and every reading
          builds the same candidates of the same file and asked the same
          filter questions again (on a Rust-derived input, seven questions
          over sequences that each used the whole of their 5 s, 35 s per
          reading).  An answer is reused for a question that prints as the
          same formula, with the same free variables at the same sorts, up to
          the reader's fresh [#tvar] names, so its validity is the same; or
          for the question at the same position of a reading's filter
          questions with the same order-blind fingerprint, which holds when
          the readings build the same candidates in the same order, as the
          probe's candidate index already presumes (a re-reading can list a
          disjunction's members in another order, since sets are ordered by
          the fresh names).  An undecided answer is kept too, so a later
          reading never drops a candidate an earlier one kept.  Only which
          filter questions are asked changes, and a [sat] of the probe holds
          for any candidate.  Measured: enforced, the probe read five
          candidates of a Rust-derived input in 48 s where it read three in
          116 s.  [false]: each reading asks again *)
  filter_skips_quantified_seq : bool; [@default false]
      (** a candidate filter question that is not quantifier-free and
          mentions a sequence is not asked, and keeps its candidate, as an
          undecided one does.  Such a question is refuted only by a
          countermodel of a universally quantified formula over sequence
          reads, which Z3 5.1.0 was not seen to build: on a Rust-derived
          input each of the seven filter questions of a reading (candidates
          quantified over integers whose bodies read sequences) used its
          whole 5 s, 35 s of a 120 s run, and each was still undecided after
          60 s replayed alone.  Only which candidates are tried can change
          (a candidate a refutation would have dropped is tried, its solve
          spending time); a [sat] of the probe holds for any candidate.
          Every filter question's shape and outcome is counted in the phase
          report ([ub-filter-shape/...]) whatever this field is *)
  quantified_candidates : bool; [@default true]
      (** [false]: a candidate that defines one of the unknowns by a
          formula that is not quantifier-free is not solved, and the probe
          ends there (each target's candidates come quantifier-free first, so
          every later one is quantified too or leaves the target undefined).
          A quantified definition puts its quantifier into every constraint
          the unknown occurs in, and the problem left is one the zero-unknown
          check can prove only by instantiating it.  On the Rust-derived
          inputs where a closure's postcondition is left to inference, every
          candidate is quantified (over integers and sequences, with sequence
          reads beneath), none of seven was proved or refuted at 150 s,
          and the first was still unproved at 1,161 s; over 477 Rust-derived
          inputs at 120 s the switch acted on 10, answering the same ones.
          Only the probe's [sat] can be lost, and only where it would have
          come from a quantified candidate.  [true] (the default): every
          candidate is solved in turn *)
}
[@@deriving yojson]

(** The inner-Skolem refutation probe: with an [.smt2] input whose reading
    made a functional witness of an existential, read the file again with each
    witness given only the universals its existential's body mentions
    ([reader.skolem_body_variables_only], set for that reading alone), and run
    the preprocessing's refuting stages on it -- the finite instantiation of a
    quantified sort among them -- without solving it.  When they reduce it to
    [false], [unsat] is the answer; anything else is discarded and the problem
    is solved as given, with every witness at its full arity.  Only [unsat] is
    read, and it is sound: the two readings are equisatisfiable in every model
    (inner Skolemisation), so a refutation of the reduced one refutes the
    input.  Its point is that the reduced witnesses make the finite instance a
    refutation needs far smaller (a four-element instance undecided past
    100 s is refuted in about 2 s), while the full arity is kept for the
    search for a model, whose witness is often named by exactly the universal
    the reduced reading drops.  Nothing is read again when the reduced reading
    gives every witness its full arity. *)
type inner_skolem_probe = {
  mode : probe_mode; [@default Off]
      (** [Off] (the default): not tried.  [Sequential]: before the other
          probes, its time added to every input it does not refute.
          [Raced]: in a forked copy raced against the rest, answering only
          with its [unsat] *)
  budget_ms : int; [@default 30000]
      (** the probe's cooperative deadline (strict), read between the
          preprocessing's stages *)
  finite_query_timeout_ms : int option; [@default Some 10000]
      (** the finite instantiation's budget per size inside the probe, in
          place of the preprocessor's own ([finite_forall_sorts.query_timeout_ms],
          2 s by default, chosen so that the pass delays the main solve little).
          Raced, the probe delays nothing, and the reduced instance it exists
          for sits on that edge: about 2 s standalone at four elements, and with
          the 2 s budget it refuted 2 of 3 times on a loaded machine.  [None]:
          the preprocessor's own budget *)
}
[@@deriving yojson]

(** The all-true probe: the input read again with EVERY Boolean-valued
    unknown of the ordinary kind defined as [true] (as the true-precondition
    probe defines its selection, [PCSP.Parser.define_true]), solved, and a
    [sat] of it, extended with the [true]s, is the answer.  Only [sat] is
    read, and it is sound for the true-precondition probe's reason: the
    re-read problem is the input with those unknowns replaced before its
    existentials were skolemised.  When no unknown of another kind is left the
    re-read problem has no unknown, and solving it is checking that each
    constraint holds with every unknown [true] -- a validity check, made
    before the predicate eliminator has anything to eliminate.

    The shape it is for: a constraint set every clause of which has an
    unknown application as its head and no unknown in a negative position but
    the goal's, whose body holds what the goal needs (a verifier's [assume]
    right before the asserted condition).  [true] everywhere is then a
    solution, while the problem as given spends its whole budget eliminating
    a long chain of call-result unknowns before the CEGIS loop starts (16
    such inputs answered in 12 to 36 s, against no answer in 120 s).  On an
    input where [true] everywhere is not a solution the copy's answer is
    discarded and only its CPU time is spent: on a 716-input Thrust corpus
    the copy answered 13 other inputs (3 of them otherwise unanswered in that
    run), and no answer was lost beyond single-run draws. *)
type all_true_probe = {
  mode : probe_mode; [@default Off]
      (** [Off] (the default): not tried.  [Sequential]: first of the
          probes, its time added to every input it does not answer.  [Raced]: in a forked copy raced against the rest,
          answering only with its [sat] *)
  budget_ms : int; [@default 60000]
      (** the probe's cooperative deadline, as the true-precondition
          probe's *)
}
[@@deriving yojson]

(** The repeated-premises probe ([PCSatCommon.RepeatedPremises]): solve, in
    clausal form, the problem with every clause that defines an unknown [p]
    (its head the single atom [p(..)], its body not applying [p]) stripped of
    the premises of the unknowns that every clause applying [p] in its body
    applies as well; a [sat] of that is the answer, and any other outcome is
    discarded and the problem solved as given.  Only [sat] is read, and it is
    sound: a clause without a premise implies the clause with it, so a
    solution of the stripped problem solves the input.  The shape it is for
    is a chain of call-result unknowns, each defined over the earlier ones'
    atoms that every later clause applies again: inlining them copies each
    earlier unknown once per later use, and stripped, each is defined by its
    callee's contract alone.  Nothing is solved when no premise is dropped. *)
type repeated_premises_probe = {
  mode : probe_mode; [@default Off]
      (** [Off] (the default): not tried.  [Sequential]: before every other
          probe, its time added to every input it does not answer.
          [Raced]: in a forked copy raced against everything after it,
          answering only with its [sat] *)
  budget_ms : int; [@default 60000]
      (** the probe's cooperative deadline, as the true-precondition
          probe's *)
}
[@@deriving yojson]

(** Which eligible definitions the opaque-definitions probe makes universal
    ([PCSP.Parser.opaque_selection]).  [Bodies] (the default): by their bodies,
    as [keep_quantifier_free] says.  [Goal_congruence]: the definitions
    applied both in a premise and in the conclusion of a goal assertion (one
    whose conclusion applies no unknown; a negated premise conjunct counts as
    conclusion), closed under the definitions their bodies apply, whatever
    their bodies are; [keep_quantifier_free] is not read.  It is for a goal
    whose conclusion restates its premises' defined predicates on related
    arguments: kept abstract, the goal follows by congruence, and the
    definitions on one side only keep their bodies.  Every selection is
    sound alike, since only a [sat] is read and each definition is one
    interpretation of its universal function.  [Goal_cone_congruence]: as
    [Goal_congruence], with a goal's premises extended by the premises of the
    clauses whose conclusion applies an unknown the goal's premises apply
    (one step), for goals whose facts reach them through an unknown.
    [Bodies_or_goal_congruence]: the definitions either [Bodies] or
    [Goal_congruence] chooses. *)
type opaque_selection =
  | Bodies
  | Goal_congruence
  | Goal_cone_congruence
  | Bodies_or_goal_congruence
[@@deriving yojson]

(** The opaque-definitions probe: with an [.smt2] input file, read the file
    again with each eligible definition ([define-fun] with parameters whose
    body reaches no unknown) a universal function without a body, added to
    the dependency set of every later DQ unknown that already depends on
    every universal function the body reaches
    ([PCSP.Parser.opaque_definitions_sexps]), and solve that; a [sat] of it
    is the answer, and any other outcome is discarded.  Sound because the
    definition is one interpretation of the universal function, chosen per
    model as a function of the universals its unknowns may depend on.  Tried
    only when the caller reads no solution (no printed, checked or returned
    solution), since the solution found names the universal functions. *)
type opaque_definitions_probe = {
  mode : probe_mode; [@default Raced]
      (** [Raced] (the default): in a forked copy against the rest, answering
          only with its [sat]; [Off]: not tried.  Why raced by default: on
          Thrust goals whose conclusion follows from defined predicates by
          their names (a premise restated up to equalities, a precondition
          the caller's contract states), the reading answers in 1-171 s where
          the input with the definitions unfolded gets no answer in 300 s,
          and on the inputs it acts on it lost no answer and no measured
          time.  It acts only through [-p pcsp] (and [-p chc]) on an [.smt2]
          file, the one entry that hands PCSat its file name.  Raced, the
          copy's presence at the preprocessor's duplicate checkpoint once
          changed the process's own refutation, which the digest computed in
          a forked copy removed; a raced probe relies on that *)
  selection : opaque_selection; [@default Bodies]
      (** which eligible definitions are made universal ([opaque_selection]) *)
  also_raced : opaque_selection list; [@default []]
      (** further selections, each raced in a copy of its own beside
          [selection]'s, with [mode] [Raced] only.  The names every selection
          would make universal are computed in the process before the first
          copy is forked, and a further selection's copy is forked only when
          its set is non-empty and differs from [selection]'s and from every
          earlier further selection's, so a selection that would re-solve a
          reading already raced costs no copy.  Each copy answers only with
          its [sat], sound on its own whatever the selection (see
          [selection]).  Why two copies rather than one union selection: on
          Thrust goals the larger abstraction of [Bodies_or_goal_congruence]
          defeats inputs that [Goal_cone_congruence] alone answers, and
          [Goal_cone_congruence] alone picks nothing on inputs that [Bodies]
          answers *)
  keep_quantifier_free : bool; [@default true]
      (** with [selection] [Bodies] or [Bodies_or_goal_congruence]: make
          universal (by the body) only the definitions whose body has a
          quantifier, and keep quantifier-free ones (datatype testers and
          discriminators, arithmetic abbreviations), whose unfolding the
          solver decides cheaply, defined *)
  budget_ms : int; [@default 60000]
      (** the probe's cooperative deadline, as for the true-precondition
          probe *)
}
[@@deriving yojson]

(** The probes: re-readings or variants of the input solved before (or
    raced against) the problem as given, each reading only a verdict that is
    sound on its own.  In order: opaque definitions, repeated premises,
    inner Skolem, upper-bound definition, least definition, witness seed,
    true precondition, lower bound, then the problem as given. *)
type probes = {
  upper_bound_definition : upper_bound_definition_probe;
      [@default
        Common.Util.config_default upper_bound_definition_probe_of_yojson "{}"]
  least_definition : least_definition_probe;
      [@default Common.Util.config_default least_definition_probe_of_yojson "{}"]
  witness_seed : witness_seed_probe;
      [@default Common.Util.config_default witness_seed_probe_of_yojson "{}"]
  true_precondition : true_precondition_probe;
      [@default Common.Util.config_default true_precondition_probe_of_yojson "{}"]
  all_true : all_true_probe;
      [@default Common.Util.config_default all_true_probe_of_yojson "{}"]
  lower_bound : lower_bound_probe;
      [@default Common.Util.config_default lower_bound_probe_of_yojson "{}"]
  inner_skolem : inner_skolem_probe;
      [@default Common.Util.config_default inner_skolem_probe_of_yojson "{}"]
  repeated_premises : repeated_premises_probe;
      [@default
        Common.Util.config_default repeated_premises_probe_of_yojson "{}"]
  opaque_definitions : opaque_definitions_probe;
      [@default
        Common.Util.config_default opaque_definitions_probe_of_yojson "{}"]
  relax_linear_walk : bool; [@default true]
      (** whether the lower-bound relaxation ([PCSP.Parser.lower_bound_relax],
          read by the lower-bound and the least-definition probes) collects
          its occurrences with the walk linear in a clause's length, which
          builds a side condition only beneath a recorded occurrence and
          shares the nested sides of a disjunction's tail, instead of
          rebuilding the side of the rest of a disjunction at every disjunct.
          The relaxation is the same up to the names of fresh variables: a
          substitution into a bound that renames a captured binder draws a
          fresh name, and the old walk made such draws in side conditions it
          then discarded, so the two can number their fresh variables
          differently (and order name-ordered binder lists differently).
          Linear against cubic on a generated 400-disjunct clause (0.11
          against 5.9 s); on the inputs measured the walk took under 1 s
          either way, the bounds' closing being the cost.  On by default:
          equal up to fresh names is the same meaning *)
  ladder_skips_unread_stages : bool; [@default false]
      (** while a probe solves its problem, the zero-unknown verdict does not
          run the stages whose only possible answer is the one the probe
          discards ([PCSatCommon.NoUnknownLadder.read]): for the lower-bound
          probe, which reads only [unsat], the sequence instantiation (early
          and late), which can only prove; for the true-precondition,
          least-definition, witness-seed and upper-bound probes, which read
          only [sat], every pin (early and late), which can only refute.  No
          answer a probe reads is lost or gained by it, since each stage is
          sound on its own; what changes is the time a probe takes before it
          gives up, in either direction (a skipped stage that would have
          decided early leaves the later stages to run to their budgets).
          [false]: every probe's verdict runs the whole ladder *)
  deadline_in_preprocessing : bool; [@default false]
      (** whether the predicate eliminator reads a probe's strict deadline
          (its [budget_ms]): without it a probe whose preprocessing outlasts
          its budget runs on until the preprocessing ends, and the problem as
          given is solved only after that *)
  deadline_at_stages : bool; [@default false]
      (** whether the stage boundaries outside the predicate eliminator read
          a probe's strict deadline: the boundaries between the
          preprocessing's passes, between building the CEGIS loop's phases
          and before the synthesizer's initialisation, and the qualifier
          generator's loops over predicates and clauses.  A passed deadline
          there ends the probe, whose answer is discarded.  Without it a
          probe whose preprocessing ends inside its budget can spend the rest
          of a run building templates, none of which reads the deadline *)
  races_in_process_when_large : bool; [@default false]
      (** a [Raced] probe runs in this process, in its sequential place,
          instead of in a forked copy whenever the fork's copy-on-write cost
          does not fit: when this process's major heap is larger than the
          least headroom ([memory.max - memory.current]) of its memory
          cgroups ([Common.ForkGuard.fork_fits]); since the shared memory
          budget a raced probe that does not fit is not started and runs in
          its sequential place with the field off as well
          ([PCSatCommon.ParallelRace.start]), so the field changes only the
          phase's name.  A forked OCaml copy writes every page of the live
          heap while its collector marks, so it holds a second copy of the
          heap within seconds of its first major cycle; past the headroom
          that copy is what a memory cap kills.  The answers are those of the
          sequential order either way (a probe reads only a verdict that is
          sound on its own); in process the probe's time is added to the
          run's.  With no readable limit the copy is made as before *)
  copy_nice : int; [@default 0]
      (** the niceness a [Raced] probe's forked copy adds to itself right
          after the fork ([PCSatCommon.ParallelRace.lower_priority]), and the
          questions those copies fork; not the Houdini pre-pass's copy and
          not the process.  A probe reads one verdict only and on most inputs
          reads none -- the true-precondition probe can answer only a
          satisfiable input, and on the Thrust corpus its copy answered in
          fewer than one run in six while running beside the process, often
          long past its own budget -- so under load its copy takes CPU from
          the process, and from every other run on the machine, that the
          process could use.  Niceness changes only when the copy computes,
          never what: an answer it gives is the one it gave before, and an
          answer lost is one whose wall-clock deadline or solver budget fired
          before the copy got the CPU to reach it.  On an idle machine
          nothing changes.  That cost falls where a probe works: an input
          only the true-precondition probe answers, past its budget, was
          answered in 1 of 2 runs at niceness 19 on two contended cores
          against 2 of 2 at 0, while once the true-precondition probe's
          [skip_forced_only] removes the copies that only repeat the
          process's solve, the rest carry little CPU.  [0]: the copies run at
          the process's priority *)
}
[@@deriving yojson]
(** When the program forces a full major collection before it makes a new Z3
    context.  The questions asked are the same under every rule; the
    collector's timing is not, and Z3's models can depend on it (finalisers
    release terms), so a model, and with it a later example, may differ.
    Process-wide once a configuration sets a rule. *)
type z3_collections =
  | By_count of {
      new_context : int; [@default 8]
          (** force the collection before every n-th new Z3 context rather
              than before each (n = 1); see
              [Z3interface.set_new_context_full_major_every].  A value of 1
              leaves the process-wide count as it is *)
      seq_axiom : int; [@default 8]
          (** force the collection before the fresh Z3 context of every n-th
              sequence-axiom fallback question only, rather than before each
              (n = 1); see [Z3interface.set_seq_axiom_full_major_every].  A
              value of 1 leaves the process-wide count as it is.  Only
              [proved] is read from those questions, so what can change is
              the time a question has left under its budget, and how many
              dropped fallback contexts wait for the collector (at most n).
              Why: over a heap of 1-2 GB the collection took about a second
              per question, most of the fallback's time on a large
              Rust-derived input (an elimination and the argument-sharing
              pass each spent 45-55 s in it) *)
    }
      (** count rules; the default, 8 for both *)
  | By_bytes of {
      bytes : int;
          (** force the collection only when the program has allocated at
              least this many bytes in the OCaml major heap since the last
              forced collection (and before the first context), in place of
              every count rule -- both of [By_count] and a stage's own
              every-n (the known-function context admission's); see
              [Z3interface.set_new_context_full_major_bytes].  A byte count,
              not a time.  It does not bound the number of dropped contexts
              waiting for the collector *)
    }
  | By_z3_memory of {
      megabytes : int;
          (** force the collection only when Z3's own estimate of the native
              memory it holds has grown by at least this many megabytes over
              the lowest reading since the last forced collection, in place
              of every count rule and of [By_bytes]; see
              [Z3interface.set_new_context_full_major_z3_mb].  It bounds what
              it is for: the native memory of dropped contexts waiting for
              the collector stays under this many megabytes at every new
              context *)
    }
[@@deriving yojson]

(** Where a question that needs a context of its own
    ([check_sat ~fresh_solver:true], the sequence-axiom fallback) is asked. *)
type z3_pool =
  | Fresh_contexts  (** a fresh context each time; the default *)
  | Clean_pool of {
      max_uses : int; [@default 64]
          (** a clean context is retired after this many questions (see
              [Z3interface.set_clean_pool_max_uses]) *)
    }
      (** a clean pooled context reused through [Z3.Solver.reset], so that no
          new context and no forced full major collection is made for it
          while the pool has one waiting; a context in which a recursive
          function was ever declared never returns to the pool (see
          [Z3interface.lease_clean_instance]).  Process-wide once a
          configuration sets it.  A reset solver in such a context decided
          what a fresh context decided on the quantified goal it was measured
          on; what can change is the terms' identifiers, and with them which
          draw a heavy-tailed question gets *)
[@@deriving yojson]

(** Handing Z3 an integer that is a bit-vector in disguise as a bit-vector
    ([Z3interface.set_int_to_bv_range]). *)
type z3_int_to_bv =
  | No_int_to_bv  (** integers are handed to Z3 as integers *)
  | Range of {
      mod_pow2 : bool; [@default false]
          (** the conversion also moves [int_to_bv n] into a remainder
              [mod a 2^k]: the low [k] bits of the moved [a] when [k < n],
              the moved [a] itself otherwise (exact, the remainder being
              Euclidean); see [Z3interface.push_int2bv] *)
      twins : bool; [@default false]
          (** the rewrite before a satisfiability question also names each
              integer the top-level conjuncts bound to [[0, 2^n)] by a
              bit-vector, adds a bit-vector twin of each top-level integer
              literal over such integers, and reads [int_to_bv] of a
              translated term as the low bits of its translation; see
              [Z3interface.int_to_bv_twins_subst].  Equisatisfiable, models
              mapped back *)
      split_ask_original : bool; [@default false]
          (** a question whose split rewrite needed an integer quotient is
              asked, after the strengthening with every quotient fixed to 0,
              as given rather than split; equisatisfiable, so only the form
              handed to Z3 changes; see
              [Z3interface.set_int_to_bv_split_ask_original] *)
    }
      (** before a satisfiability question goes to Z3, a free integer [x]
          under [int_to_bv n] becomes [ubv_to_int] of a fresh bit-vector
          (when top-level bounds put it in [[0, 2^n)]) or is split into a
          bit-vector and a quotient, which is first asked fixed to 0; such a
          question is asked in a fresh context; and every conversion moves
          [int_to_bv] inside [+], [-], [*] and drops it on [ubv_to_int] of
          its own width.  Equisatisfiable, models mapped back.  The default.
          Each switch is process-wide once on *)
[@@deriving yojson]

(** The words questions ([Z3interface.check_valid_by_words], asked by the
    predicate eliminator and the zero-unknown verdict) and the translation of
    bounded integer arithmetic to bit-vectors.  Each switch is process-wide
    once on. *)
type z3_words = {
  interface : bool; [@default true]
      (** a words question is first asked in its separated form
          ([Z3interface.int_to_bv_interface_subst]): every word read through
          [int_to_bv] of an integer term forgotten, no bounded integer
          replaced by a word, and only facts true in every model relating the
          two worlds (congruence, order on [[0, 2^m)], literals, ring
          equations modulo [2^m]) added; a weakening of the negation, of
          which only [unsat] is read.  Why: a bit-mask obligation (bit
          [i mod 64] of a word against the same bit of the word masked to
          [d mod 64] bits, [i < d]) ran past 60 s in every form the words
          question had and was [unsat] in under a second so separated.  What
          it costs: one more question per words question it does not prove.
          On by default: on the inputs it acts on it lost no answer and gave
          no other verdict *)
  seq_as_arrays : bool; [@default true]
      (** a words question is asked with each sequence built from variables
          and selectors read as an array and a length, and with every
          conjunct still holding a sequence dropped
          ([Z3interface.seq_reads_as_arrays]): a weakening of the negation,
          of which only [unsat] is read, so only a proof is taken.  Why: Z3's
          sequence solver gave up ("reached max unfolding") on such questions
          of a bit-set obligation under some seeds, and so weakened they were
          [unsat] in 0.5-1 s under every seed *)
  pow2_shifts : bool; [@default true]
      (** in the translation of bounded integer arithmetic to bit-vectors
          (the twins of [Range]'s [twins] and the words questions), a [div]
          or [mod] by a power of two is written as a shift or a mask instead
          of a division circuit; exact (see
          [Z3interface.int_to_bv_pow2_shifts]) *)
}
[@@deriving yojson]

(** The Z3 boundary: how questions are handed to Z3, where they are asked,
    and when the collector runs around its contexts.  Every member is
    process-wide: a configuration that leaves a switch off does not switch
    off what another one turned on. *)
type z3 = {
  collections : z3_collections;
      [@default Common.Util.config_default z3_collections_of_yojson {|["By_count", {}]|}]
  pool : z3_pool; [@default Fresh_contexts]
  seq_axiom_fallback_ms : int option; [@default Some 500]
      (** the budget, in milliseconds, of a second attempt at a validity
          question over sequences that the native theory leaves undecided,
          asked with the sequences as an uninterpreted sort and axioms about
          length, reads and concatenation, and read only when it proves the
          question valid ([null]: no second attempt).  It reaches every
          validity check of the process: the preprocessor's, the
          zero-unknown verdict's and [check_solution]'s.  On by default at
          500 ms: on the Thrust corpus it answers two iterator-extension
          queries in every run that the native theory leaves undecided in
          almost every run, each proof returning in well under that budget,
          while a query it cannot prove spends the whole budget -- at 2000 ms
          nineteen such queries were most of a 58 s run -- and the 500 ms
          budget lost no answer over the corpus; see
          [Z3interface.with_seq_axiom_fallback] *)
  seq_axiom_fork : bool; [@default false]
      (** ask each sequence-axiom fallback question in a forked copy of the
          process, killed after three times its budget (at least 1 s), so
          that the context it needs is made and released in the copy and this
          process makes no context and forces no full major collection for
          it; see [Z3interface.ask_seq_axiom_question].  The copy asks the
          same question in the same kind of fresh context and only a proof is
          read back, so the setting changes where the question runs, not what
          it can answer; what can change is a proof lost to the kill; where
          no copy can be made (other domains running) the question is asked
          in process as before.  The last configuration loaded decides.  Off
          by default because of memory: the full collections it no longer
          forces had also kept the heap compact, and on inputs with a 1-2 GB
          heap the peak resident size rose up to 1.7 times *)
  flat_and_or : bool; [@default false]
      (** hand Z3 a nest of conjunctions (disjunctions) as one n-ary [and]
          ([or]) over its operands rather than as the nest of binary ones;
          see [Z3interface.set_flat_and_or].  The formula asked is the same,
          but its text is not, so the dumped questions differ in nesting *)
  flat_long_and_or_min : int option; [@default Some 1000]
      (** [Some n]: a nest of conjunctions (disjunctions) with at least [n]
          operands is handed to Z3 as one n-ary [and] ([or]) even with
          [flat_and_or] off; see [Z3interface.set_flat_long_and_or_min].
          Z3 flattens a binary nest when it asserts it, at a cost quadratic
          in the nest's length: with holes of 3,413 qualifiers, asserting a
          run's synthesis constraints took 6.6-17.1 s as binary nests and
          0.4-1.0 s n-ary.  The formula asked is the same; a question
          without such a nest reaches Z3 as the same term as with [None],
          which is why a threshold and not [flat_and_or]: that changes every
          question's term and measured 22 % slower in total *)
  left_to_right_creation : bool; [@default false]
      (** create the Z3 terms of every application's operands from the
          first to the last, as Z3's reader does, rather than the last first,
          as OCaml's evaluation order makes the conversion do; see
          [Z3interface.set_left_to_right_creation].  Every question is the
          same term either way, but Z3 orders operands and decision atoms by
          creation, so its search can differ *)
  int_to_bv : z3_int_to_bv;
      [@default Common.Util.config_default z3_int_to_bv_of_yojson {|["Range", {}]|}]
  words : z3_words; [@default Common.Util.config_default z3_words_of_yojson "{}"]
  unsigned_linear_bv_templates : bool; [@default true]
      (** read a bit-vector parameter of a linear template by its unsigned
          integer value, so the template is integer-linear
          ([c0 + sum ci * ubv_to_int xi >= 0]), rather than by the signed
          value of a wrapping bit-vector product; see
          [Ast.LogicOld.bv_unsigned_linear_templates].  A different
          hypothesis space, not a different question about a candidate, so
          soundness is not at stake.  On by default: with it, a bit-vector
          loop whose invariant counts over a word was answered where the
          wrapping reading answered nothing, and no input lost an answer.
          Inert on a problem with no bit-vector-sorted predicate parameter *)
  qelim_max_subst_growth : int option; [@default None]
      (** bound the tree a variable elimination by substitution may build,
          as the size of the substituted term times the occurrences it
          replaces; an elimination over the bound is declined and its
          disequality stays; see [Ast.Qelim.max_subst_growth] *)
}
[@@deriving yojson]
type t = {
  (* main configuration *)
  coordinator : Coordinator.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/coordinator/tbq_ar.json"]
  preprocessor : Preprocessor.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/preprocessor/enable.json"]
  sol_printer : SolPrinter.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/sol_printer/enable.json"]
  load_oracle_sol : bool; [@default false]
      (** read a known solution for some unknowns from [<dir>/<basename>.sol],
          [<basename>] the input file's name without its extension. It is
          given to the version space; the labeler reads it only under its
          [ORACLE_SAT] strategy, and the template synthesizer's
          [oracle_example_probe] reads it without acting on it. *)
  oracle_sol_dir : string option; [@default None]
      (** the directory [<dir>] above; [null] reads the current directory *)
  oracle_sol_smtlib2 : bool; [@default false]
      (** read the file as SMT-LIB2 [define-fun]s, one per unknown, in the
          scope of the input file's own declarations (datatypes, quantified
          sorts), with the unknown's parameters in the problem's order -- a
          dependency-quantified unknown's universals first, sorted by name,
          then its declared arguments. When off, the file is read as SyGuS
          [define-fun]s, whose sorts are atoms only. *)
  solve_each_query : bool; [@default false]  (** solve each query independently *)
  check_problem : bool; [@default false]  (** check the well-formedness of the input pfwCSP *)
  check_solution : bool; [@default false]  (** check the correctness of the output solution *)
  witness : PCSatCommon.WitnessConfig.t;
      [@default PCSatCommon.WitnessConfig.default]
      (** what to record for sat/unsat witnesses; all on by default *)
  z3 : z3; [@default Common.Util.config_default z3_of_yojson "{}"]
      (** the Z3 boundary (see [z3]) *)
  probes : probes; [@default Common.Util.config_default probes_of_yojson "{}"]
      (** the probes and how they are run (see [probes]) *)
  races : races; [@default Common.Util.config_default races_of_yojson "{}"]
      (** what a probe raced in a forked copy may be stopped for, and how a
          copy takes the computation over (see [races]) *)
  reader : reader; [@default Common.Util.config_default reader_of_yojson "{}"]
      (** how an [.smt2] input is read (see [reader]) *)
  recursive_functions : recursive_functions;
      [@default Common.Util.config_default recursive_functions_of_yojson "{}"]
      (** what is done with the input's recursive functions (see
          [recursive_functions]) *)
  simplifier : simplifier; [@default Common.Util.config_default simplifier_of_yojson "{}"]
      (** the simplifier's and the evaluator's process-wide switches (see
          [simplifier]) *)
  seq_as_array_check_solution : bool; [@default false]
      (** with [check_solution], ask each constraint whose sequence terms are
          in the translation's fragment (no [seq.extract]) and whose reads are
          range-guarded as arrays plus a length
          first ([Z3interface.check_sat_seq_as_array], an equisatisfiable
          translation), and untranslated when that is undecided or the
          constraint is outside the fragment; when off, the checker's questions
          are asked as they are *)
  retry_undecided_check_solution : bool; [@default true]
      (** with [check_solution], a constraint the checker's Z3 query leaves
          undecided (after the sequence-instance attempt) is asked again, of Z3
          under a variable-eliminating tactic and of cvc5 with enumerative
          instantiation, 5 s each ([WitnessChecker.valid_by_stronger_routes]);
          only an [unsat] of the negation is read, and it turns "unchecked"
          into "passed".  Checker-only: it changes no answer, only how many
          constraints of a [sat] answer the report confirms. *)
  matched_forms_check_solution : bool option; [@default None]
      (** with [check_solution], whether the checker's sequence-instance
          attempt also asks each piece's matched-instance forms
          ([WitnessChecker.valid_by_instances]), aligned with the earlier
          pieces when the coordinator's
          [zero_unknown.matched_instances.aligned_hyps] is on.  [None]
          follows the coordinator's [zero_unknown.matched_instances.forms],
          so that the checker can re-prove a constraint by the forms the
          zero-unknown verdict proved it with; [Some b] overrides.
          Checker-only: only a proof is read, so it changes no answer, only
          how many constraints the report confirms. *)
  context_admission : context_admission;
      [@default Common.Util.config_default context_admission_of_yojson "{}"]
      (** the known-function context admission at the SMT-LIB file entry (see
          [context_admission]) *)
  ground_range_expansion : int option; [@default None]
      (** [Some w]: in truth-table cells and validation questions, an integer
          quantifier whose range is bounded by two numerals at most [w] apart
          is replaced by the disjunction or conjunction of its instances
          ([Ast.RangePin.expand_ground], an equivalence in every model).
          Process-wide once set.  [None]: questions are asked as built *)
  phase_time_report : bool; [@default false]
      (** print a wall-clock account of the run by phase on stderr, one line
          per phase, at exit and when the process is stopped by SIGTERM or
          SIGINT ([Common.PhaseTime]): preprocessing by step, predicate
          elimination with its validity questions and the sequence-axiom
          fallback, the Houdini pre-pass, each CEGIS phase, the zero-unknown
          verdict's stages, and the time inside Z3's check calls under each.
          A diagnostic: it changes no answer.  Process-wide once on.  It
          starts one watcher thread (not a domain, which would forbid the
          forked queries' fork), and a forked copy sends no report. *)
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  let open Or_error in
  Coordinator.Config.load_ext_file cfg.coordinator >>= fun coordinator ->
  Preprocessor.Config.load_ext_file cfg.preprocessor >>= fun preprocessor ->
  SolPrinter.Config.load_ext_file cfg.sol_printer >>= fun sol_printer ->
  Ok { cfg with coordinator; preprocessor; sol_printer }

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "PCSat"
  let instantiate = instantiate_ext_files
end)
