open Core
open Common.Util
open Coordination
open Preprocessing

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
  z3_fresh_retry : Z3Smt.Z3interface.fresh_retry_policy;
      [@default Z3Smt.Z3interface.Off]
      (** whether a quantified Z3 query the pooled, incremental-mode context
          leaves undecided is asked again in a fresh context ([RetryOnUnknown]),
          every quantified query goes to a fresh context ([AlwaysFresh], for
          measurement), or neither ([Off]). The setting is process-wide and
          defaults to [RetryOnUnknown]; [Off] here means "leave the process-wide
          setting as it is", so it cannot switch the retry off. *)
  seq_axiom_fallback : int option; [@default Some 500]
      (** the budget, in milliseconds, of a second attempt at a validity
          question over sequences that the native theory leaves undecided,
          asked with the sequences as an uninterpreted sort and axioms about
          length, reads and concatenation, and read only when it proves the
          question valid ([null]: no second attempt). Process-wide once set,
          and it reaches every validity check of the process: the
          preprocessor's, the zero-unknown verdict's and [check_solution]'s.
          On by default at 500 ms: on the Thrust corpus it answers two
          iterator-extension queries in every run that the native theory
          leaves undecided in almost every run, each proof returning in well
          under that budget, while a query it cannot prove spends the whole
          budget -- at 2000 ms nineteen such queries were most of a 58 s run --
          and the 500 ms budget lost no answer over the corpus; see
          [Z3interface.with_seq_axiom_fallback]. *)
  true_precondition_probe : string list; [@default []]
      (** the true-precondition probe ([PCSatCommon.TruePrecondition]): with a
          non-empty list and an [.smt2] input file, first read the file again
          with each named unknown (Boolean, of the ordinary kind) defined as
          [true] and solve that; a [sat] of it, extended with the [true]s, is
          the answer, and any other outcome -- [unsat] included -- is discarded
          and the problem is solved as given.  Only [sat] is read, and it is
          sound: a solution of the substituted problem together with
          [p := true] is a solution of the original.  The substitution is made
          before the reader's skolemisation, which an unknown under an
          existential triggers.  [[]]: no probe *)
  true_precondition_probe_witness_causing : bool; [@default true]
      (** the true-precondition probe without names: the unknowns tried as
          [true] are, beside any [true_precondition_probe] names, those that
          occur beneath a quantifier existential in effect (a written [exists]
          at a positive position, a written [forall] at a negative one) --
          exactly the unknowns that make the reader skolemise a quantifier into
          a functional predicate ([PCSP.Parser.witness_causing_unknowns]).  The
          selection decides only what is tried; the answer read is still only a
          [sat] of the substituted problem, sound for the reason given above.
          [false]: only the named unknowns *)
  true_precondition_probe_parallel : bool; [@default true]
      (** run the true-precondition probe in a forked copy of the process,
          concurrently with the problem solved as given (and the lower-bound
          probe before it), instead of before them
          ([PCSatCommon.ParallelRace]): the first answer wins, the copy's
          being only the probe's [sat].  A cooperative budget does not bound
          a phase that does not return, so the sequential probe can take more
          than its budget away from the problem as given -- measured, a probe
          whose zero-unknown check ran 125 s past a 60 s budget -- and the
          race removes that cost at the price of a second process.  When the
          process cannot fork (it has spawned a domain) the probe runs
          sequentially as without this.  [false]: sequential *)
  true_precondition_probe_skip_forced_only : bool; [@default true]
      (** the true-precondition probe gives up at once, answering nothing,
          when every unknown it would define as [true] is one the forced-true
          reading ([define_forced_true]) already defined as [true] -- which is
          the case on an input with no witness-causing unknown and a forced one,
          since the probe re-reads the input with the forced unknowns defined
          too.  Its problem is then the problem the process solves as given,
          so it could answer only what that solve answers; raced, it was a
          second process solving the same problem (without the Houdini
          pre-pass, which a solve under a deadline skips) beside the first.
          On the Thrust corpus that was 125 of 172 inputs and 83% of the probe
          copies' time, and on the five such inputs the copy used to answer
          first the process answered alone in 10 of 10 runs, no slower.
          [false]: the probe solves the re-read problem whatever it defines *)
  race_drop_duplicate_copies : bool; [@default true]
      (** a probe raced in a forked copy whose problem, once preprocessed, is
          the problem the process solves (up to fresh names) is dropped: the
          copy leaves, or the process kills it, whichever side reaches the
          comparison second ([PCSatCommon.ParallelRace.Duplicate]).  Such a
          copy asks the process's questions one for one -- on a Rust-derived
          input whose unknowns preprocessing eliminates, the true-precondition
          copy asked all 310 of the process's solver checks, in the same
          order, for the whole run -- so on a loaded machine it halves the
          process's speed and gives nothing the process does not.  Only a copy
          is stopped, never an answer; the process's answers are the
          sequential order's with the probe finding nothing.  [false]: every
          raced copy runs to its end *)
  race_drop_duplicates_early : bool; [@default true]
      (** with [race_drop_duplicate_copies], compare a raced copy's problem
          with the process's also right after the predicate elimination,
          before the refutation-only passes that follow it (the unknown-free
          sweep, the unfolding refutation, the finite instantiation), which
          return the problem they are given unless they refute it.  A copy
          found a duplicate there leaves before asking those passes' questions
          a second time; one that is not is compared again after the whole
          preprocessing, as without the switch.  Only a copy is stopped, never
          an answer.  Why: on two Rust-derived inputs the true-precondition
          copy, found a duplicate after the whole preprocessing, had spent
          most of it in those passes (about ten of fifteen seconds at idle)
          beside the process doing the same *)
  race_two_claims : bool; [@default false]
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
  true_precondition_probe_budget_ms : int; [@default 60000]
      (** the probe's cooperative deadline (strict: read at the loop's phase
          boundaries and by the synthesizer), which does not bound a phase that
          does not return; the problem solved under it also skips the Houdini
          pre-pass, as every solve under a deadline does *)
  lower_bound_probe : string list; [@default []]
      (** the lower-bound probe: with a non-empty list and an [.smt2] input
          file, after the true-precondition probe (when that is on) read the
          file again with each named unknown (Boolean, of the ordinary kind)
          replaced by [true] where it is demanded and by a lower bound derived
          from the input's own constraints where it is assumed
          ([PCSP.Parser.lower_bound_relax]), and solve that; an [unsat] of it
          is the answer, and any other outcome is discarded and the problem
          solved as given.  Only [unsat] is read, and it is sound: the read
          problem is a relaxation, every solution of the input in a model
          restricting to one of it in that model.  [[]]: no unknown named;
          the probe is still on, by default, for the unknowns
          [lower_bound_probe_witness_causing] selects, and is off only when
          this list is empty and that field is [false] *)
  lower_bound_probe_witness_causing : bool; [@default true]
      (** the lower-bound probe without names: beside the named unknowns,
          those that occur beneath a quantifier existential in effect, as for
          [true_precondition_probe_witness_causing].  [false]: only the named
          ones *)
  lower_bound_probe_skip_unrelaxable : bool; [@default true]
      (** the lower-bound probe is not made, and its reading of the input is
          not taken, when an earlier reading of the same file under the same
          reader switches, with the same unknowns defined as [true] (the
          forced-true reading, [define_forced_true]), shows that the
          relaxation would relax nothing: no named unknown and no
          witness-causing unknown that is Boolean-valued and of the ordinary
          kind ([PCSP.Parser.relaxable_known]).  The probe reading then builds
          the same assertions, its relaxation returns no relaxed unknown, and
          the probe discards it unread, so skipping it changes no answer and
          no question; it removes a whole reading of the input.  With no such
          earlier reading, the probe reads as without this.  [false]: the
          probe always reads *)
  lower_bound_probe_parallel : bool; [@default false]
      (** run the lower-bound probe in a forked copy of the process,
          concurrently with the problem solved as given, instead of before it
          ([PCSatCommon.ParallelRace]); the first answer wins, the copy's
          being only the probe's [unsat].  As for
          [witness_seed_probe_parallel], the probe's budget does not bound
          its preprocessing, so sequentially its whole time is added to every
          input it does not answer -- every satisfiable one.  When the process
          cannot fork the probe runs sequentially.  Read only when the probe
          is on ([lower_bound_probe] or
          [lower_bound_probe_witness_causing]).  [false]: sequential *)
  witness_seed_probe : bool; [@default true]
      (** first solve the problem with every functional witness of a guarded
          body universal [forall q. lo <= q < hi => ...] defined as the last
          index, [w(x, r) := r = hi - 1] ([PCSatCommon.WitnessSeed]), under
          [true_precondition_probe_budget_ms]; a [sat] of it, extended with
          the definitions, is the answer, and any other outcome is discarded
          and the problem solved as given.  Only [sat] is read, and it is
          sound: each definition is a total, single-valued function, so it is
          one choice of the witness.  [false]: no such probe *)
  witness_seed_probe_parallel : bool; [@default false]
      (** run the witness-seed probe, seeds included, in a forked copy of the
          process, concurrently with everything after it (the true-
          precondition and lower-bound probes and the problem as given),
          instead of before them ([PCSatCommon.ParallelRace]); the first
          answer wins, the copy's being only the probe's [sat], extended with
          the seeds.  The budget does not bound the probe's preprocessing or
          its zero-unknown check, so sequentially a probe that runs long
          delays every input it does not answer by all of its time.  When the
          process cannot fork the probe runs sequentially.  Read only when
          [witness_seed_probe] is on.  [false]: sequential *)
  witness_seed_filter_disjuncts : bool; [@default true]
      (** with [witness_seed_probe], the bounds are read converting only the
          disjuncts of a clause's pure part that mention the witness's last
          argument, rather than the whole pure part once per witness atom
          ([PCSatCommon.WitnessSeed.disjuncts_mentioning]); the seeds are the
          same.  Why: on Rust-derived inputs with large pure parts the
          whole-part conversion took 87 s to more than 300 s before any
          solving began *)
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
  name_quantified_premises : bool; [@default false]
      (** the input is read with every quantified premise that would multiply a clause's
          clausal form -- a written [forall] at a negative position whose negated body holds a
          conjunction mentioning an unknown -- replaced by a fresh unknown of the ordinary kind
          over its free term variables, defined by [premise => fresh] beside it
          ([PCSP.Parser.premise_definitions]), before skolemisation.  Equisatisfiable in every
          model, so both verdicts are read; the fresh unknowns are kept from every
          preprocessing elimination ([PCSP.Parser.premise_unknowns_of]), which would otherwise
          put the product back.  [false]: read as written *)
  law_reach_dependents : bool; [@default true]
      (** on by default, because it is the reading the laws state: without it an assertion that applies an unknown depending on
          a law's function, but does not write the function, demands the
          unknown for unlawful interpretations too.  With an [.smt2] input
          file, read it again with a [:law] premise of
          a universal function also inserted into every assertion that
          applies an unknown depending on that function (one whose
          [declare-dep-exists-fun] list names it, or a plain [declare-fun]
          when the function is Bool-valued), and solve that instead.  More
          premises, so every solution of the problem as read solves this one,
          and every solution of this one solves the problem the laws state
          ("for every lawful interpretation"); an [unsat] of it is one of the
          stated problem when every law is closed and some interpretation is
          lawful (an open law assumes only its instance at the clause's
          variables, a stronger clause).  [check_solution] checks against
          this re-read problem, the one solved.  [false]: the
          law reaches only the assertions that mention its function, directly
          or through definitions *)
  law_dedup_premises : bool; [@default true]
      (** the SMT-LIB reader inserts each [:law] premise without the conjuncts
          the assertion already assumes (another function's copy of the same
          law, a conjunct the law repeats, an antecedent the clause already
          has): the same problem up to [c /\ c = c], with fewer quantified
          premises.  It is the reader's default; with an [.smt2] input,
          [false] re-reads the input with every law inserted whole, once per
          function reaching the assertion, and solves that instead
          ([check_solution] checks against the re-read problem).  Applies to
          [law_reach_dependents]'s re-read as well *)
  law_read_once : bool; [@default true]
      (** with an [.smt2] input and [-p pcsp], set the reader's switches that
          [law_reach_dependents], [law_dedup_premises] and
          [onepoint_constructor_binders] ask for before the input is first
          read, and keep that problem instead of reading the input a second
          time for them.  The problem is the one the second reading gives, up
          to fresh names.  The first reading also keeps its assertions until
          [define_forced_true] has asked which unknowns every solution makes
          [true], and that reading is made only when the answer is not empty
          (an empty answer discards it).  On by default: the problem kept is
          the re-reading's, digest for digest and with the same fresh names
          drawn when both readings start from the same counters.
          [false]: read as given, then read again when a switch asks for it *)
  forced_true_release_given : bool; [@default false]
      (** with [law_read_once] and [define_forced_true], when the kept
          assertions of the first reading name at least one unknown every
          solution makes [true], the problem of the first reading is let go
          before the input is read with them defined, instead of being held
          beside that reading: afterwards only its signature is read (to
          extend a [sat] with the [true]s).  The problem solved is the same.
          Should that reading raise, the input is read again as at first (the
          same problem up to fresh names) and solved as given.  It frees
          nothing when [check_solution] keeps the problem for the checker.
          [false]: the first problem is held until that reading returns *)
  rec_fun_graph_unknowns : bool; [@default true]
      (** replace each application of a counted recursive function (a
          [define-fun-rec] whose body is [ite (k <= c) base step] with one
          recursive call at [k - 1], every other argument passed on) by an
          ordinary unknown for the graph of the applications at one counter
          term, with a base and a step clause ([PCSP.RecFunGraph.encode];
          equisatisfiable), and drop from the problem's function environment
          the definitions the result no longer applies.  A property of such a
          function stated with no unknown leaves the induction that proves it
          to the zero-unknown validity check, which no SMT solver does; as an
          unknown it is an invariant the synthesiser looks for, as in the loop
          spelling of the same function.  [false]: the problem as given.
          On by default *)
  rec_fun_graph_unknown_free_only : bool; [@default false]
      (** with [rec_fun_graph_unknowns], encode only the constraints that
          mention no unknown, keeping every other constraint as it is (still
          equisatisfiable: each constraint is encoded on its own).  A
          function applied only beside unknowns that predicate elimination
          removes is then left to the validity question that remains after
          elimination, which may need no induction, instead of becoming a
          recursive unknown that stops elimination.  [false]: every
          constraint with a counted application is encoded *)
  rec_fun_graph_every_reading : bool; [@default false]
      (** with [rec_fun_graph_unknowns], encode every problem a re-reading of
          the input gives (the forced-true reading, and the readings the
          least-definition, true-precondition and lower-bound probes solve)
          as the problem read first is encoded, so that the encoding is in
          force on every path whichever reading is solved.  Contract: on
          each path the problem solved is [PCSP.RecFunGraph.encode] of that
          path's reading with this configuration's arguments, and every
          verdict stays sound (the encoding is equisatisfiable).  [false]:
          a re-read problem is solved as read, so an unknown forced [true]
          by an unrelated clause switches the encoding off *)
  rec_fun_graph_after_preprocessing : bool; [@default true]
      (** with [rec_fun_graph_unknowns], encode the problem the preprocessor
          hands the CEGIS loop instead of the problem as read, and only its
          clauses that mention no unknown THERE
          ([PCSP.RecFunGraph.encode_clauses ~unknown_free_only:true]): a
          clause whose unknowns predicate elimination removed is encoded, one
          that still has an unknown is not.  The read-time encoding is then
          not applied on any path, so no constraint is encoded twice.  Every
          reading of the input (the forced-true one and the probes') reaches
          the loop through the preprocessor, so the decision is the same on
          every path.  Contract and equisatisfiability: [encode_clauses]; the
          problem preprocessing recorded its eliminations against is not
          changed, so completing a solution with the eliminated predicates is
          as without the switch.  [false]: the encoding, when on, is applied
          at read time.  On by default, together with
          [rec_fun_graph_after_elimination] *)
  rec_fun_graph_after_elimination : bool; [@default true]
      (** with [rec_fun_graph_after_preprocessing], apply that encoding right
          after predicate elimination (the preprocessor's [post_elim] hook)
          rather than to the problem the preprocessor hands the CEGIS loop:
          the clauses it encodes are the same kind (mention no unknown once
          elimination has run), and the graph unknowns then go through the
          passes after elimination -- argument reduction and sharing, and
          the word ranges put around the solver call -- as read-time graph
          unknowns do.  Equisatisfiable for the same reason; an added
          unknown is reduced like one the elimination added.  Before the
          encoding the clauses that mention no unknown are swept for a
          refutation (an invalid one is then answered [unsat] at once rather
          than through the loop building the graph unknown's chain).  With
          the preprocessor disabled the hook is not reached and nothing is
          encoded.  [false]: the
          encoding is applied after the last preprocessing pass, where no
          such pass sees the graph unknowns (a 64-bit word argument of a
          graph unknown then gets no range invariant).  On by default *)
  rec_fun_graph_dynamic : bool; [@default false]
      (** with [rec_fun_graph_unknowns], encode after preprocessing a clause
          that applies a counted function when validation leaves it undecided
          (the solver neither confirms nor refutes a candidate on it), and
          solve again ([PCSatCommon.RecFunDynamic] has the contract).  Only
          clauses of the problem the preprocessor handed on are encoded, each
          at most once, so the restarts are finitely many.  The examples of
          clauses still present are kept (the solver context's version
          reuse), those derived from an encoded clause are dropped, and the
          function environment is kept whole.  Like
          [rec_fun_graph_after_preprocessing] it turns the read-time encoding
          off; the two may be on together.  [false]: an undecided clause
          rejects the candidate and nothing is learnt from it *)
  rec_fun_graph_candidates : bool; [@default false]
      (** with [rec_fun_graph_unknowns], give every graph unknown introduced
          the atoms [r_i = f(a_i, j)] stating its intended solution, the
          graph of the calls it replaces, as declared candidate atoms
          (qualifiers of its hypothesis space and the Houdini pre-pass's
          starting conjunction), and keep the functions they apply in the
          problem's environment.  The graph solves the encoding's base and
          step clauses and turns its goal back into the original constraint,
          so an encoded constraint is reachable from what the unencoded one
          offers.  Hints only: no constraint changes.  [false]: the graph
          unknown starts from the hypothesis space alone and the function
          leaves the environment when nothing applies it *)
  reconstruct_rec_functions : bool; [@default false]
      (** turn each eligible ordinary unknown (it occurs only in its defining
          clauses, which mention no other unknown, and as a premise
          elsewhere; the last argument is the result) back into the
          recursive function its defining clauses compute, when the
          clauses' guards are proved mutually exclusive and exhaustive and
          the function is proved total (a lexicographic structural or
          integer measure decreasing at every recursive call), and add that
          function to the function environment and its applications to the
          vocabulary of the template and the Houdini pre-pass
          ([PCSatCommon.RecFunReconstruct.reconstruct]).  The unknown stays
          an unknown.  Only enlarges the hypothesis space; a predicate whose
          checks are not all proved is left as it is.  [false]: no
          reconstruction *)
  reconstruct_names_apart : bool; [@default false]
      (** with [reconstruct_rec_functions] or [rec_function_lemmas], draw the
          pass's fresh term-variable names from a counter of its own
          ([reconstruct ~names_apart:true]), so the process-global counter is
          where it was before the pass and the rest of the run names what it
          builds as it would without the pass.  Exact: the pass's result is
          the same up to the names it draws.  [false]: the pass draws from the
          global counter *)
  reconstruct_replace_predicates : bool; [@default false]
      (** with [reconstruct_rec_functions], also replace each reconstructed
          unknown [rho(a, b)] by [b = f(a)] and drop its defining clauses
          (equisatisfiable for a total function: the unknown's least
          solution is the function's graph, and it occurs elsewhere only as
          a premise).  [false]: the unknown stays *)
  reconstructed_fun_quals : int; [@default 16]
      (** with [reconstruct_rec_functions], at most this many qualifiers per
          unknown applying a reconstructed function at the terms its
          parameters reach (as [rec_fun_app_quals] states, with also
          [x = f(t)] for a Boolean parameter [x] and a Bool-valued [f]), in
          the template and in the Houdini pre-pass alike *)
  rec_function_lemmas : bool; [@default false]
      (** prove, for each recursive function shown total (an input
          [define-fun-rec] or a reconstructed one), the jointly inductive
          subset of candidate invariants from its signature (an integer
          result's sign and its order against integer arguments and
          sequence lengths, a sequence result's length, a Boolean result's
          implications with argument testers), and record them as the
          function's property, which every query applying the function
          conjoins at each application.  Each lemma is proved valid by
          induction over the measure that showed totality; nothing unproved
          is recorded.  [false]: no lemma *)
  lower_bound_probe_rounds : int; [@default 2]
      (** how many rounds the lower bounds are iterated from [false]; each
          round lets a bound use the bounds of the unknowns a demand of it
          assumes *)
  least_definition_probe : bool; [@default true]
      (** the least-definition probe: with an [.smt2] input file, before the
          witness-seed probe, read the file again with every unknown that
          makes the reader skolemise a quantifier
          ([PCSP.Parser.witness_causing_unknowns]) defined, at every
          occurrence, as the lower bound the input's own constraints give it
          after [least_definition_probe_rounds] rounds
          ([PCSP.Parser.lower_bound_define]), and solve that under
          [true_precondition_probe_budget_ms]; a [sat] of it, extended with
          the definitions, is the answer, and any other outcome is discarded
          and the problem solved as given.  Only [sat] is read, and it is
          sound: the definitions are one choice of those unknowns.  The guess
          suits a closure's precondition and postcondition left to inference
          and assumed by a library loop beneath a universal: the least
          solution of the postcondition is what the closure's body gives,
          while a skolemised witness of the universal would have to name an
          index at which the closure accepted, which no term over the clause's
          variables is.  On by default.  [false]: no such probe *)
  least_definition_probe_parallel : bool; [@default true]
      (** run the least-definition probe in a forked copy of the process,
          concurrently with everything after it (the witness-seed, true-
          precondition and lower-bound probes and the problem as given),
          instead of before them ([PCSatCommon.ParallelRace]); the first
          answer wins, the copy's being only the probe's [sat].  The probe
          never answers an unsatisfiable input, so sequentially its whole
          time -- a full preprocessing and zero-unknown check of the defined
          problem, under a cooperative budget that does not bound a phase
          that does not return -- is added to every such input.  When the
          process cannot fork the probe runs sequentially.  Read only when
          [least_definition_probe] is on.  [false]: sequential *)
  least_definition_probe_rounds : int; [@default 3]
      (** the rounds of [least_definition_probe]'s lower bounds; each round
          lets a bound use the bounds of the unknowns a demand of it assumes,
          so a postcondition established from a fact through k intermediate
          unknowns needs k + 1.  A Thrust closure's body reaches its
          postcondition through two (the body's entry and its result), and a
          round more than needed adds the disjuncts of the occurrences beneath
          a head universal, quantified, which the definition drops again but
          which cost reading time to build *)
  lower_bound_probe_budget_ms : int; [@default 60000]
      (** the probe's cooperative deadline, as for
          [true_precondition_probe_budget_ms] *)
  probe_deadline_in_preprocessing : bool; [@default false]
      (** whether the predicate eliminator reads the strict deadline of the
          true-precondition and lower-bound probes
          ([true_precondition_probe_budget_ms], [lower_bound_probe_budget_ms]):
          without it a probe whose preprocessing outlasts its budget runs on
          until the preprocessing ends, and the problem as given is solved only
          after that *)
  probe_races_in_process_when_large : bool; [@default false]
      (** a probe switched to a race ([least_definition_probe_parallel],
          [witness_seed_probe_parallel], [true_precondition_probe_parallel],
          [lower_bound_probe_parallel]) runs in this process, in its
          sequential place, instead of in a forked copy whenever the fork's
          copy-on-write cost does not fit: when this process's major heap is
          larger than the least headroom ([memory.max - memory.current]) of
          its memory cgroups ([Common.ForkGuard.fork_fits]).  A forked OCaml
          copy writes every page of the live heap while its collector marks,
          so it holds a second copy of the heap within seconds of its first
          major cycle; past the headroom that copy is what a memory cap
          kills.  The answers are those of the sequential order either way
          (a probe reads only a verdict that is sound on its own); in process
          the probe's time is added to the run's.  With no readable limit the
          copy is made as before *)
  probe_copy_nice : int; [@default 0]
      (** the niceness a raced probe's forked copy adds to itself right after
          the fork ([PCSatCommon.ParallelRace.lower_priority]): the copies of
          [least_definition_probe_parallel], [witness_seed_probe_parallel],
          [true_precondition_probe_parallel] and [lower_bound_probe_parallel],
          and the questions those copies fork; not the Houdini pre-pass's copy
          and not the process.  A probe reads one verdict only and on most
          inputs reads none -- the true-precondition probe can answer only a
          satisfiable input, and on the Thrust corpus its copy answered in
          fewer than one run in six while running beside the process, often
          long past its own budget -- so under load its copy takes CPU from
          the process, and from every other run on the machine, that the
          process could use.  Niceness changes only when the copy computes,
          never what: an answer it gives is the one it gave before, and an
          answer lost is one whose wall-clock deadline or solver budget fired
          before the copy got the CPU to reach it.  On an idle machine nothing
          changes.  That cost falls where a probe works: an input only the
          true-precondition probe answers, past its budget, was answered in 1
          of 2 runs at niceness 19 on two contended cores against 2 of 2 at 0,
          while once [true_precondition_probe_skip_forced_only] removes the
          copies that only repeat the process's solve, the rest carry little
          CPU.  [0]: the copies run at the process's priority *)
  lower_bound_probe_max_input_bytes : int; [@default 4_000_000]
      (** the probe is not tried on an input file larger than this many
          bytes.  It reads the whole file a second time, and its relaxation
          walks each clause with a side condition per disjunction it passes,
          which grows with the square of a clause's length: on a 25 MB input
          the second reading and the walk had not finished after 220 s and
          then exhausted 6 GB, where the inputs the probe answers are under
          250 KB and the largest of the others measured under 2.5 MB.
          Skipping it changes no answer, only whether an [unsat] is found
          this way. *)
  lower_bound_relax_linear_walk : bool; [@default true]
      (** whether the lower-bound relaxation ([PCSP.Parser.lower_bound_relax],
          read by [lower_bound_probe] and [least_definition_probe]) collects
          its occurrences with the walk linear in a clause's length, which
          builds a side condition only beneath a recorded occurrence and
          shares the nested sides of a disjunction's tail, instead of
          rebuilding the side of the rest of a disjunction at every disjunct.
          The relaxation is the same up to the names of fresh variables: a
          substitution into a bound that renames a captured binder draws a
          fresh name, and the old walk made such draws in side conditions it
          then discarded, so the two can number their fresh variables
          differently (and order name-ordered binder lists differently).
          Linear against cubic on a generated 400-disjunct clause (0.11 against
          5.9 s); on the inputs measured the walk took under 1 s either way,
          the bounds' closing being the cost.  On by default: equal up to
          fresh names is the same meaning *)
  z3_new_context_full_major_every : int; [@default 8]
      (** force a full major collection before every n-th new Z3 context
          rather than before each ([1], the default); see
          [Z3interface.set_new_context_full_major_every].  Process-wide once a
          configuration sets a value other than 1.  The questions asked are the
          same; the collector's timing is not, and Z3's models can depend on it
          (finalisers release terms), so a model, and with it a later example,
          may differ. *)
  z3_new_context_full_major_bytes : int option; [@default None]
      (** [Some b]: force the full major collection before a new Z3 context
          only when the program has allocated at least [b] bytes in the OCaml
          major heap since the last forced collection (and before the first
          context), in place of every count rule: this field's sibling
          [z3_new_context_full_major_every], a stage's own every-n and
          [z3_seq_axiom_full_major_every]; see
          [Z3interface.set_new_context_full_major_bytes].  Process-wide once a
          configuration sets it.  The threshold is a byte count, not a time.
          The questions asked are the same; the collector's timing is not, so
          a model may differ, as under the count rule.  It does not bound the
          number of dropped contexts waiting for the collector. *)
  z3_clean_reset_pool : bool; [@default false]
      (** ask a question that needs a context of its own
          ([check_sat ~fresh_solver:true], the sequence-axiom fallback) in a
          clean pooled context reused through [Z3.Solver.reset] instead of a
          fresh one, so that no new context and no forced full major collection
          is made for it while the pool has one waiting; a context in which a
          recursive function was ever declared never returns to the pool (see
          [Z3interface.lease_clean_instance]).  Process-wide once a
          configuration sets it.  A reset solver in such a context decided what
          a fresh context decided on the quantified goal it was measured on;
          what can change is the terms' identifiers, and with them which draw
          a heavy-tailed question gets. *)
  z3_clean_reset_pool_max_uses : int; [@default 64]
      (** with [z3_clean_reset_pool], a clean context is retired after this
          many questions (see [Z3interface.set_clean_pool_max_uses]) *)
  z3_seq_axiom_full_major_every : int; [@default 8]
      (** force the full major collection before the fresh Z3 context of every
          n-th sequence-axiom fallback question only, rather than before each
          ([1], the default); see [Z3interface.set_seq_axiom_full_major_every].
          Process-wide once a configuration sets a value other than 1.  The
          questions asked are the same and only [proved] is read from them, so
          what can change is the time a question has left under its budget,
          and how many dropped fallback contexts wait for the collector (at
          most n).  Why: over a heap of 1-2 GB the collection took about a
          second per question, most of the fallback's time on a large
          Rust-derived input (an elimination and the argument-sharing pass
          each spent 45-55 s in it). *)
  z3_seq_axiom_fork : bool; [@default false]
      (** The copy asks the same question in the same kind of fresh context
          and only a proof is read back, so the setting changes where the
          question runs, not what it can answer.  Off by default because of
          memory: the full collections it no longer forces had also kept the
          heap compact, and on inputs with a 1-2 GB heap the peak resident
          size rose up to 1.7 times.  Ask each
          sequence-axiom fallback question in a forked copy of the process,
          killed after three times its budget (at least 1 s), so that the
          context it needs is made and released in the copy and this process
          makes no context and forces no full major collection for it; see
          [Z3interface.ask_seq_axiom_question].  Process-wide once a
          configuration is loaded.  What can change is a proof lost to the
          kill; where no copy can be made (other domains running) the question
          is asked in process as before. *)
  z3_flat_and_or : bool; [@default false]
      (** hand Z3 a nest of conjunctions (disjunctions) as one n-ary [and]
          ([or]) over its operands rather than as the nest of binary ones;
          see [Z3interface.set_flat_and_or].  Process-wide once a
          configuration turns it on.  The formula asked is the same, but its
          text is not, so the dumped questions differ in nesting. *)
  z3_int_to_bv_range : bool; [@default true]
      (** hand Z3 an integer that is a bit-vector in disguise as a
          bit-vector: before a satisfiability question goes to Z3, a free
          integer [x] under [int_to_bv n] becomes [ubv_to_int] of a fresh
          bit-vector (when top-level bounds put it in [[0, 2^n)]) or is split
          into a bit-vector and a quotient, which is first asked fixed to 0;
          such a question is asked in a fresh context; and every conversion
          moves [int_to_bv] inside [+], [-], [*] and drops it on
          [ubv_to_int] of its own width.  Equisatisfiable, models mapped back;
          see [Z3interface.set_int_to_bv_range].  Process-wide once a
          configuration turns it on. *)
  bv_unsigned_linear_templates : bool; [@default true]
      (** read a bit-vector parameter of a linear template by its unsigned
          integer value, so the template is integer-linear
          ([c0 + sum ci * ubv_to_int xi >= 0]), rather than by the signed
          value of a wrapping bit-vector product; see
          [Ast.LogicOld.bv_unsigned_linear_templates].  A different
          hypothesis space, not a different question about a candidate, so
          soundness is not at stake.  On by default: with it, a bit-vector
          loop whose invariant counts over a word was answered where the
          wrapping reading answered nothing, and no input lost an answer.
          Inert on a problem with no bit-vector-sorted predicate parameter.
          Process-wide once on: a configuration setting it [false] does not
          turn it off in a process where another solver turned it on. *)
  z3_int_to_bv_mod_pow2 : bool; [@default false]
      (** with [z3_int_to_bv_range] on, the conversion also moves
          [int_to_bv n] into a remainder [mod a 2^k]: the low [k] bits of the
          moved [a] when [k < n], the moved [a] itself otherwise (exact, the
          remainder being Euclidean); see [Z3interface.push_int2bv].
          Process-wide once on.  Inert without [z3_int_to_bv_range]. *)
  z3_int_to_bv_twins : bool; [@default false]
      (** with [z3_int_to_bv_range] on, the rewrite before a satisfiability
          question also names each integer the top-level conjuncts bound to
          [[0, 2^n)] by a bit-vector, adds a bit-vector twin of each top-level
          integer literal over such integers, and reads [int_to_bv] of a
          translated term as the low bits of its translation; see
          [Z3interface.int_to_bv_twins_subst].  Equisatisfiable, models
          mapped back.  Process-wide once on.  Inert without
          [z3_int_to_bv_range]. *)
  z3_int_to_bv_pow2_shifts : bool; [@default true]
      (** in the translation of bounded integer arithmetic to bit-vectors
          (the twins of [z3_int_to_bv_twins] and the words questions of
          [Z3interface.check_valid_by_words]), a [div] or [mod] by a power of
          two is written as a shift or a mask instead of a division circuit;
          exact (see [Z3interface.int_to_bv_pow2_shifts]).  Process-wide once
          on. *)
  z3_words_seq_as_arrays : bool; [@default true]
      (** a words question ([Z3interface.check_valid_by_words], asked by the
          predicate eliminator and the zero-unknown verdict) is asked with
          each sequence built from variables and selectors read as an array
          and a length, and with every conjunct still holding a sequence
          dropped ([Z3interface.seq_reads_as_arrays]): a weakening of the
          negation, of which only [unsat] is read, so only a proof is taken.
          Why: Z3's sequence solver gave up ("reached max unfolding") on such
          questions of a bit-set obligation under some seeds, and so weakened
          they were [unsat] in 0.5-1 s under every seed.  Process-wide once
          on. *)
  eval_recursive_qualifiers_ground : bool; [@default false]
      (** a truth-table cell whose qualifier applies a defined function is
          first rewritten by unfolding the definitions along their guards
          ([Evaluator.unfold_rec_apps]); the rewritten qualifier, which applies
          no defined function, replaces the original when the unfolding
          completes, and the cell is evaluated as before otherwise
          ([PCSatCommon.TruthTable.eval_recursive_qualifiers_ground]).  Exact:
          each step is an instance of the definition's equation.  At a ground
          example the value is then computed by evaluation instead of being
          asked of Z3 as a quantified question under a budget; at a parametric
          example a guard over a parameter stops the unfolding.  Process-wide
          once on. *)
  skip_induction_cells : bool; [@default false]
      (** a parametric truth-table cell whose qualifier applies a defined
          function, and whose unfolding along the definitions' guards stops at
          a guard reading one of the example's parameters (the value needs
          induction), is left undecided without asking the solver, as a
          timed-out question leaves it
          ([PCSatCommon.TruthTable.skip_induction_cells]).  Sound as a timeout
          is; it can leave undecided a cell the solver would have decided.
          Independent of [eval_recursive_qualifiers_ground].  Process-wide
          once on. *)
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
  prune_unreached_definitions : bool; [@default false]
      (** the problem the CEGIS loop starts from (after preprocessing, and in
          each nested solve) keeps in its own function environment
          ([Params.fenv]) only the definitions its clauses reach and the size
          functions ([PCSP.Problem.prune_unreached_definitions]).  The template
          hypothesis space applies every other function of that environment to
          the parameters' terms, so an unused recursive definition became
          qualifiers whose truth at a parametric example Z3 had to decide by
          unfolding the recursion, past the query's own timeout: a linear loop
          answered in 2 s gave no answer in 60 s with one unused
          [define-fun-rec] beside it.  The clauses are unchanged; the
          hypothesis space loses the applications of definitions nothing
          applies. The process-global environment is untouched. Dropping
          definitions is not a general full-context equivalence: unused
          recursive equations can be inconsistent or constrain shared symbols.
          Preservation requires an extension satisfying the omitted equations;
          the reachability walk does not check that condition. *)
  declare_reached_functions_only : bool; [@default false]
      (** declare to Z3 only the defined functions a query reaches (directly,
          or through another reached function's definition or recorded
          property), in the pooled entry points of [Z3interface] and in the
          synthesis phase's long-lived instances, instead of every function of
          the problem's environment ([Z3interface.fenv_for_query],
          [Z3interface.declare_reached]).  A definition registered with a
          context changes Z3's answers there even when nothing applies it: a
          linear loop answered in 2 s stalled in synthesis with one unused
          recursive definition beside it. Reached functions are declared and
          defined as before, but absence from converted formulas does not make
          an omitted defining equation irrelevant. Full-context equivalence
          requires a model-extension condition that this switch does not check.
          Process-wide once enabled; a later false configuration does not
          reset it. *)
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
  simplify_normal_forms : bool; [@default false]
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
  hspace_normalize_memo : bool; [@default false]
      (** keep the normal form [HypSpace.qualifiers_of] gives each qualifier
          (simplify, normalise, simplify), per domain and keyed by the
          qualifier, so that a qualifier met again in another unknown's
          hypothesis space or a later rebuild is not normalised again
          ([HypSpace.normalize_memo]).  The three steps are functions of the
          formula alone, so the qualifiers are the same.  Process-wide, only
          ever switched on.  Why: on a Rust-derived input of 23 unknowns whose
          parameters bear the same names, the first hypothesis-space update
          spent 82 s of 120 s normalising qualifiers it had normalised for
          the previous unknown. *)
  simplify_skip_simplified : bool; [@default false]
      (** a conditional lifted out of an application simplifies only the nodes
          the lift built, taking its already simplified parts as they are;
          meaning-preserving, the same output wherever each part is a fixed
          point of the simplifier (always, on random formulas, together with
          [simplify_normal_forms]).  Process-wide once on, set when the solver
          is configured; see [Ast.Evaluator.simplify_skip_simplified] *)
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
  seq_as_array_check_solution : bool; [@default false]
      (** with [check_solution], ask each constraint whose sequences are
          concat-free and whose reads are range-guarded as arrays plus a length
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
          [matched_instance_aligned_hyps_no_unknown_query] is on.  [None]
          follows the coordinator's [matched_instance_forms_no_unknown_query],
          so that the checker can re-prove a constraint by the forms the
          zero-unknown verdict proved it with; [Some b] overrides.
          Checker-only: only a proof is read, so it changes no answer, only
          how many constraints the report confirms. *)
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
  monotonic_deadlines : bool; [@default false]
      (** measure the solver's durations and deadlines (the nested solve's
          deadline, the probes', the pre-pass's and the ladder's budgets, the
          traced timings) on CLOCK_MONOTONIC instead of the time of day
          ([Common.Clock]).  The time of day can be stepped by a time
          synchronisation, a deadline taken on it then firing up to a step
          early against the solver's own budgets and `timeout`, which count
          on the monotonic clock.  Process-wide, and decided by the first
          PCSat configuration a process applies, so a nested solve's
          configuration cannot change it. *)
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
