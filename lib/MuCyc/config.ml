open Core
open Common.Util

(* definitions for software model checking [PLDI'24] *)

type cex_typ = QE | Model | MBP of int
(* 0 : use latest, 1 : use saved, 2 : use saved loop invariant *)
[@@deriving yojson]

type com_typ =
  | Or
  | Return of bool (* cex accumulation *)
  | Yield of
      bool (* query weakening *) * bool (* share trace among coroutines *)
[@@deriving yojson]

type strategy = Solve | Refine of cex_typ * com_typ [@@deriving yojson]
type cshare = Level | Global of bool (* use saved *) [@@deriving yojson]

type induct =
  | Normal of bool (* use disjuncts *)
  | Light of bool (* use disjuncts *)
[@@deriving yojson]

(* Which proof search decides a CHC-shaped muCLP problem.
   [Frame_search] is the bottom-up, Spacer-style frame search (with the
   top-down variant of [top_down_search]); [Relational] is the induction-based
   proof search of Unno, Torii and Sakamoto, "Automating Induction for Solving
   Horn Clauses" (CAV 2017), which unfolds, applies induction hypotheses and
   folds lemmas, and reads the fields marked "relational verification" below.  The frame search is the
   default: it is the one every shipped configuration has run. *)
type proof_search = Frame_search | Relational [@@deriving yojson]

(* definitions for QSMT solving *)

(* The level [j'] a lemma learned at level [j] returns to (the model-based projection
   of the unsat core eliminates levels [j - 1] and deeper, so every free variable of the
   lemma lies at level [j - 2] or below).  Odd levels are existential and even levels
   universal, so the levels of [j]'s parity are those of the player who lost at [j].
   [Deepest_own_variable]: the level of the deepest free variable of the lemma that
   belongs to that player (1 or 2 if none), as in Bjorner and Janota (LPAR 2015,
   Algorithm 1); a free variable of the other player may lie deeper.
   [Chronological]: always [j - 2].
   [Deepest_own_variable_projected]: [Deepest_own_variable]'s level, the lemma's
   variables deeper than it projected away once.
   [Deepest_own_variable_projected_repeatedly]: the same, repeated (projecting below
   the new level and taking its deepest own variable again) until the level no longer
   changes, so the lemma mentions no variable deeper than the level returned to.
   [Deepest_any_variable]: the level of the deepest free variable of the lemma of
   either player, moved one level deeper when it has the other parity: the lowest
   level of [j]'s parity that no free variable of the lemma lies deeper than, the
   lemma kept as projected.  This is the return Bocevska, Tsukada, Unno, Padon and
   Shoham (CAV 2026, Section 6.2) propose in place of [Deepest_own_variable]'s, which
   may return below a free variable of the other player and then fail to make
   progress; the paper asks for the largest such level of {j - 2, j - 4, ...}, which
   read literally is always [j - 2] ([Chronological]), so the lowest one is taken.
   For [j >= 3] every choice returns to a level of [j]'s parity at most [j - 2]. *)
type backtrack_strategy =
  | Deepest_own_variable
  | Chronological
  | Deepest_own_variable_projected
  | Deepest_own_variable_projected_repeatedly
  | Deepest_any_variable
[@@deriving yojson]

(* A store, per predicate, of the cubes the blocking loop found blocked,
   indexed by the level (frames counted from the bottom) at which they were
   blocked.  [seed_by_level]: a call at level [j] seeds the cubes recorded at
   [j] without a check and checks once those recorded only at [j - 1] (a
   push).  Sound because, along one search thread, a frame is only ever
   replaced by a formula implying it, and a frame's body is monotone in the
   frames below, so a cube blocked at level [j] stays blocked there.  Used
   only under the [Or] and [Return] strategies, on the queries over
   bit-vectors and Booleans that the cube cache serves.
   [level_solvers = n] (0: off): keep up to [n] Z3 solvers, one per
   (predicate, level), across blocking calls instead of one emptied per call.
   Each antecedent a solver is asked under is asserted once, as the
   implication from a fresh selector, and a check assumes the selector of
   the call's antecedent; asserting differs from a fresh solver only in the
   solver's history, so every answer keeps its meaning (models and cores, and
   with them the search path, may differ).  The antecedent's quantified
   variables are then named by their position, so that the same frames give
   the same antecedent.  Same restrictions as [seed_by_level].
   [bit_level] (only with [level_solvers > 0]): the cube checks of a call
   served by a kept solver are asked of one propositional instance per
   domain holding the bit-blasted antecedents and literals instead (see
   [BitFrame.checker]); a formula it declines (a sort other than Booleans
   and bit-vectors, a quantifier, a function) sends the check to Z3 as
   without it.  The answers and cores mean what Z3's do.
   [incremental_exit] (independent of the other fields): the blocking loop's
   exit check (is the conjunction of the lemmas so far consistent with the
   query's negated right side?) is asked of one Z3 solver per call in the
   call's context, holding the negated right side and each lemma asserted
   once, as it is learned, instead of a fresh pooled question per round.  The
   lemma set only grows within a call, so the solver's assertions are always
   exactly the round's question and no scope is opened; only the solver's
   history differs, so every answer keeps its meaning (models, and with them
   the next cube, may differ).
   [exit_simple_solver] (only with [incremental_exit]): that solver is Z3's
   simple solver (its incremental core without the preprocessing tactics the
   default solver applies to a first check) instead of the default one.  It
   is given the same assertions, so its answers mean what the default
   solver's do; models may differ.
   [lazy_nonlinear] (only with [bit_level]): a leaf the propositional
   instance bit-blasts has its divisions and remainders that are not ground
   and its multiplications of two non-numerals (the applications whose
   circuit is quadratic in the width) replaced by fresh words, their
   non-numeral arguments held equal to fresh
   words too, and an operator's own circuit is added only when a [sat]
   model of a check violates it, the solve then being repeated (lazy
   bit-blasting with abstraction, as in Niemetz, Preiner and Zohar,
   "Scalable Bit-Blasting with Abstractions", CAV 2024).  The abstraction
   only removes constraints, so [unsat] and its cores keep their meaning,
   and [sat] is answered only on a model satisfying every definition of the
   leaves it makes true; so the answers mean what [bit_level]'s do.
   [definition_templates] (only with [lazy_nonlinear]): a definition
   added on demand is encoded through the CNF templates of
   [leaf_templates] (one per operator, numerals and width, Z3 asked once
   per template); the clauses are a CNF of the same definition, so the
   answers mean what [lazy_nonlinear]'s do.
   [lazy_nonlinear_relevant] (only with [lazy_nonlinear]): a round adds
   only the violated definitions the model's value of the checked formulas
   depends on: from the assumed literals through the and/or nodes (one
   true member of a disjunction), into a [let]'s body, and from a leaf
   into the definition of each [let]-bound word its value reads, entering
   one branch of an [ite] and one absorbing argument of a conjunction,
   disjunction, [bvand] or [bvor] (or a zero factor of [bvmul]).  [sat] is
   answered when none is left, the unreached [let]-bound words and
   abstracted results then being recomputable from their definitions
   without changing any value read; so the answers mean what
   [lazy_nonlinear]'s do.
   [kept_bit_models] (only with [bit_level]): the words' values of each
   model of a call's [sat] check are kept for the call, and a later check of
   seeding or generalisation whose literals are all true of a kept model is
   answered [sat] without a solve.  Every kept model is a model of the
   call's antecedent, so such literals have a common model with it and the
   check would have answered [sat]; the answers mean what [bit_level]'s do
   (the solver's learnt clauses and phases, and with them later models and
   cores, may differ).
   [leaf_templates] (only with [bit_level]): a leaf the propositional
   instance bit-blasts whose Z3 expression is, up to a renaming of its
   words, that of a leaf bit-blasted before is given the earlier leaf's
   clauses with the words' bits and fresh auxiliaries substituted, without
   asking Z3's tactics again (see [BitFrame.blast_templated]).  The clauses
   are a CNF of the same guarded leaf, so the answers mean what
   [bit_level]'s do (the CNF, and with it models and cores, may differ).
   [bit_domain] (only with [bit_level]): each check of the propositional
   checker decides only the variables in the cone of its assumptions (the
   variables of the clauses added for an assumed formula and, recursively,
   for its subformulas); the rest stay unassigned.  Every clause of the
   checker is guarded by a subformula's literal, so a model of the cone
   extends to the whole instance and the answers keep their meaning.
   [bit_domain_pin] (only with [bit_domain]): the cone of the call's [phi1]
   stays decided across the checks of one blocking call, so each check walks
   and switches only the cone of its cube's literals.
   [leaf_contexts] (only with [bit_level]): the leaves the propositional
   checker bit-blasts in one encoding batch (the encoding of one formula, or
   one round of definitions added by [lazy_nonlinear]) are bit-blasted in a
   Z3 context made for the batch, each leaf printed as SMT-LIB and read
   back into it, and the context is dropped at the batch's end with one
   full major collection, so that what the tactics allocate is released
   (see [BitFrame.in_batch]).  The leaf read back is the same formula, so
   its clauses are a CNF of the same guarded leaf and the answers mean what
   [bit_level]'s do.  The checker is made once per domain, so the first
   blocking call's setting holds for the domain. *)
type persistent_frames = {
  seed_by_level : bool; [@default false]
  level_solvers : int; [@default 0]
  bit_level : bool; [@default false]
  incremental_exit : bool; [@default false]
  exit_simple_solver : bool; [@default false]
  lazy_nonlinear : bool; [@default false]
  definition_templates : bool; [@default false]
  lazy_nonlinear_relevant : bool; [@default false]
  kept_bit_models : bool; [@default false]
  leaf_templates : bool; [@default false]
  bit_domain : bool; [@default false]
  bit_domain_pin : bool; [@default false]
  leaf_contexts : bool; [@default false]
}
[@@deriving yojson]

(* The two choices of how a conditional and a let-bound definition inside a
   term reach the model-based projection; their meaning is documented with the
   projection, [Interpolation.MbpProject]. *)
type projection_conditionals = Interpolation.MbpProject.projection_conditionals =
  | All_paths
  | All_paths_up_to of int
  | Model_path_for_targets
[@@deriving yojson]

type projection_lets = Interpolation.MbpProject.projection_lets =
  | Inline_lets
  | Name_subterms of {
      compare_branches : bool; [@default false]
      substitute_tainted : bool; [@default false]
    }
[@@deriving yojson]

(* One way of eliminating a counterexample's auxiliary variables (those that are
   not the predicate's arguments) when the frame search turns a model into a
   counterexample, tried in the order of [counterexample_projections]: the first
   that returns wins.
   [Mbp]: the model-based projection of [Interpolation.MbpProject]; it declines by
   raising (a rule that does not apply, an unbound variable, a failed check).
   [Model_values]: the model's value of each eliminated variable substituted (or,
   where the site keeps only the arguments, the arguments equated with their
   values); it never declines, so a step listed after it is never reached.  Its
   result is a single point of the model, so a search that keeps reaching it
   enumerates points: it costs termination, never soundness. *)
type counterexample_projection = Mbp | Model_values [@@deriving yojson]

(* One way of eliminating one non-Boolean variable of a quantifier block in the
   QSMT solver's model-based projection, tried in the order of
   [qsat_projections].  Each step either returns the projected atoms, or
   declines and hands the next step the atoms (possibly rewritten into an
   equivalent-in-the-model form that implies the original); when every step has
   declined, the theory projection's failure is raised.
   [Theory_mbp]: the projection module of the variable's sort (datatype, array,
   or the block's arithmetic theory; an uninterpreted sort has none and
   declines).  An integer variable occurring outside arithmetic positions (under
   an array read or a constructor) declines without being tried, since the
   arithmetic projection is exact only in arithmetic positions.
   [Read_over_write]: integers only; resolves the reads over stores whose index
   mentions the variable by the model (adding the index (dis)equalities that
   decide each), hands the rewritten atoms on, and tries the theory projection on
   them when the variable is then in arithmetic positions only.
   [Extensionality]: integers only; a variable occurring in a single disequality
   [a[i] != e] becomes [a != K(e)], exactly.
   [Formula_term]: a subterm of the formula free of the block, under which every
   touched atom holds in the model, substituted for the variable.
   [Model_value]: the variable's value in the model substituted; fails with an
   error for a variable of an uninterpreted sort (the model's name for an
   element is not a term), declines where the model has no value.
   Every step's result holds in the model and implies the existential closure;
   the first four are determined by the formula, so they keep the set of
   projections finite, which [Model_value] does not. *)
type qsat_projection =
  | Theory_mbp
  | Read_over_write
  | Extensionality
  | Formula_term
  | Model_value
[@@deriving yojson]

(* The model the QSMT frame search resumes with at the level [j'] a lemma returns to.
   [Reset] resumes with the empty model, so level [j'] proposes every earlier level's
   values afresh: the model reset (M <- nil) of Bjorner and Janota (LPAR 2015, Algorithm 1).
   [Keep_outer_levels] resumes with the latest model restricted to the variables of the
   levels below [j'], so the search stays in the subgame those values opened.  This goes
   towards the model reuse of Bocevska, Tsukada, Unno, Padon and Shoham (CAV 2026,
   Algorithm 7) but is not that procedure: one model is kept, the latest, not one per
   level, so an atom of the resumed strategy mentioning a variable of level [j'] or
   deeper has no value and is left out of that strategy; and [j'] is the level
   [backtrack_strategy] chooses (Algorithm 7 always returns two levels up, as
   [Chronological] does).  With [Deepest_own_variable], which may return below a free variable of
   the lemma, the kept values can lead the search into a cycle that adds the same lemma
   to the same frame forever.  Every lemma is implied by the win at the level it is added
   to whatever model the search resumes with, so the choice changes the search, not
   soundness.
   [Entry_model] is the model reuse of Algorithm 7: the search records, for each level,
   the whole model that level was last entered with (the model of the last satisfiable
   check one level up), and resumes at [j'] with the recorded model of [j'], uncut, so
   every atom of the resumed strategy has a value.  With [Chronological], [j' = j - 2]
   and the model is Algorithm 7's [M_{j-3}]; with a strategy that returns lower, the
   paper does not say which model to resume with, and the recorded model of the level
   returned to is the one used. *)
type model_after_lemma = Reset | Keep_outer_levels | Entry_model
[@@deriving yojson]

(** how the QSMT frame search keeps and updates its frames *)
type frames = {
  (* handle the outermost existential block by abstraction refinement instead of as one
     more level of the frame search: a candidate is proposed from the instances collected
     so far and checked by a fresh game with it fixed, so the check never carries the
     lemmas learned for other candidates.  Needs a variable at the outermost level and a
     third level below it; otherwise the frame search runs as usual *)
  forward : bool; [@default false]
  (* the model the search resumes with at the level a lemma returns to *)
  model_after_lemma : model_after_lemma; [@default Reset]
  update_only_atoms_j_and_before : bool; [@default false]
  update_all_frames_j_and_after : bool; [@default false]
  reuse_prev_frame : bool; [@default false]
}
[@@deriving yojson]

(* Which muCLP problem MuCyc works on.  [As_converted] takes the problem as the
   front end built it (from CHC, a transition system or a muCLP file): every
   quantifier the translation wrote is still there, and the ground-query solve
   and the proof search both see it.  [Optimize] first runs the muCLP optimizer
   ([MuCLP.Optimizer], the same rewrite MuVal and MuStrat run before their
   ground solve; [optimizer] names its configuration, by default MuVal's), and
   both steps see the optimized problem.  [rounds] is how many times it runs
   in sequence, by default two as in MuVal's default task: a round decides
   inlining on its input's call graph and leaves predicates unreached and
   arguments irrelevant that the next round removes, and a transition system
   whose ground query one round leaves behind a quantified predicate can be
   closed by the second (MuStrat runs one).  The optimizer preserves the truth
   value of the query (its header states that obligation of every step), and
   MuCyc reports only that truth value, never an interpretation of the
   predicates, so the predicates it renames, merges, inlines or shortens leave
   nothing to translate back. *)
type muclp_preprocessing =
  | As_converted
  | Optimize of {
      optimizer : MuCLP.Optimizer.Config.t ext_file;
          [@default
            Common.Util.ExtFile.Filename "./config/muclp/optimizer/enable.json"]
      rounds : int; [@default 2]
    }
[@@deriving yojson]

(* What solves each recursion-free expansion under the [Solve] strategy.
   [Chc_solver]: the expansion handed whole to [pcsp_solver] (Spacer by
   default), as MuCyc has always done.  [Interpolation (search, leaves)]: the
   expansion solved by MuCyc's own recursion-free search
   ([Interpolation.RecursionFreeChc]) over the interpolation leaves, top-down
   interpolation against the least solution, which also yields a
   counterexample when the expansion has no solution. *)
type expansion_solver =
  | Chc_solver
  | Interpolation of
      Interpolation.RecursionFreeChc.search * Interpolation.Interpolant.leaf list
[@@deriving yojson]

type t = {
  verbose : bool; [@default false]
  simplify : bool; [@default true]
  reduce : bool; [@default true]
  slice_forward : bool; [@default true]
  slice_backward : bool; [@default true]
  gen_lemmas_with_ai : bool; [@default false]
  gen_determ_conjs : bool; [@default false]
  muclp_preprocessing : muclp_preprocessing; [@default As_converted]
      (** whether the muCLP optimizer runs before the ground-query solve and
          the proof search; off by default *)
  ground_query_solve : MuCLP.GroundSolve.Config.t;
      [@default MuCLP.GroundSolve.Config.default]
      (** whether a ground query is decided before the proof search
          ([MuCLP.GroundSolve.run], which states the class, the budget and
          what an answer guarantees), on the muCLP as [muclp_preprocessing]
          leaves it; the default is every muCLP engine's, on.  It decides greatest and mixed
          fixpoints too, which the proof search refuses. *)
  pcsp_solver : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/spacer_sol.json"]
  timeout_check_valid : int; [@default 0]
  timeout_prove_each_conj : int; [@default 3]
  (* options for software model checking [PLDI'24] *)
  refinement_strategy : strategy; [@default Common.Util.config_default strategy_of_yojson {|["Refine", ["MBP", 0], ["Return", false]]|}]
  top_down_search : bool; [@default false]
      (* true: top-down proof search a la PPDP'09
         false: bottom-up proof search a la Spacer *)
  monotone_trace : bool; [@default false]
  induction : induct option; [@default None]
  (* also apply the induction rule before each counterexample computed from a
     countermodel of a clause; PLDI'24 Sec. 5.3 applies it only when a
     recursive refinement call finishes and when the trace is extended, which
     is [false].  A candidate that fails a check is dropped, so applying the
     rule more often drops candidates while the frame below is still weak *)
  induction_at_countermodels : bool; [@default true]
  (* after each refinement, frame by frame from the bottom, try to add to a
     predicate's frame the conjuncts that the frame below holds for an atom in
     the body of one of its clauses (renamed through that atom's arguments),
     each kept only when the induction rule's check passes.  A blocking
     interpolant answers only its target, so a fact the premise carries but
     the target does not ask for never reaches the successor's frame
     otherwise; Spacer's pushing moves a lemma up one level of the same
     predicate, which does not cover this *)
  premise_push : bool; [@default false]
  query_reuse : bool; [@default false]
  (* re-pose a child's query at the current level only when the child resolved
     it (returned no counterexample), as Spacer's query reuse does
     [Komuravelli et al., FMCAD 2015].  [false] re-poses it after every
     complete answer of the child, counterexample or not, which is the
     insertion point of PLDI'24 Sec. 5.3 (the end of each middle-loop
     iteration); a query whose counterexample was just found below is then
     posed again where it is reachable too *)
  query_reuse_resolved_only : bool; [@default false]
  (* under [query_reuse], end the search with a refutation when a re-posed
     query returns a counterexample.  Sound when every clause has at most one
     body atom and the thread strategy is [Or] or [Return]: a query's
     complement is then projected from the clause body and the complement of
     the parent's query alone, under the projection's contract
     ([MBP phi => exists y. phi]), so each of its states reaches a goal
     violation whatever level it is posed at; a counterexample is a set of
     reachable states.  The level at which the re-posed query is answered does
     not enter, which lets a witness longer than the current round be
     reported (IC3's re-enqueued obligations, Bradley VMCAI 2011).  Elsewhere
     the field is ignored *)
  query_reuse_refute : bool; [@default false]
  (* under [Refine (_, Return true)], accumulate the counterexamples found so
     far into the query of the first body atom only (the outer loop), as
     PLDI'24 Alg. 5 lines 10-11 do for the right premise while the left one's
     query stays the plain projection (line 14).  [false] accumulates them at
     every body atom; that only weakens a later atom's query by states already
     found reachable under the same counterexample of the earlier atoms, so
     both are sound, and they differ only on clauses with two or more body
     atoms *)
  return_accumulate_first_atom_only : bool; [@default false]
  counterexample_sharing : cshare option; [@default None]
  (* how a frame's interpolant is searched for: [Leaves] asks the leaves of
     [interpolant_leaves] in order; [Spacer_blocking b] runs Spacer's blocking
     loop first (with the state this module keeps between calls) and asks the
     leaves when it declines; see [Interpolation.Interpolant.search] *)
  interpolant_search : Interpolation.Interpolant.search;
      [@default Interpolation.Interpolant.Leaves]
  expansion_solver : expansion_solver; [@default Chc_solver]
      (** with the [Solve] strategy, what solves each recursion-free
          expansion; [Chc_solver] is the frame search as it always was *)
  expansion_shape : Interpolation.Unwinding.Config.expansion; [@default Depth]
      (** with the [Solve] strategy, how the recursive system is unwound:
          [Depth], one copy of every predicate per level (the frame search's
          own), or [Tree], one copy per occurrence path, grown where the
          solution fails to cover *)
  report_counterexample : bool; [@default false]
      (** on a refuted expansion solved by [Interpolation], hand the caller the
          refutation's derivation and model (a predicate-constraint caller
          receives it in its [unsat] answer) *)
  interpolant_leaves : Interpolation.Interpolant.leaf list;
      [@default Interpolation.Interpolant.[ Spacer_chc; Qe_weakest ]]
      (* The procedures an interpolation query is asked of, in order, each
         passing the query on when it declines: [Spacer_chc] the query as two
         Horn clauses to [pcsp_solver]; [Qe_weakest] and [Qe_strongest] one side
         projected onto the vocabulary the two share by quantifier elimination
         (the weakest end eliminates what only the consequent mentions, the
         strongest what only the antecedent mentions; both are interpolants).
         [Mbp_cover n] a disjunction of at most [n] generalised model-based
         projections of the antecedent onto that vocabulary, the projection
         run with this module's shipped [projection_conditionals] and
         [projection_lets] defaults regardless of the fields below (off unless
         listed).  [Bitwuzla_bv o] Bitwuzla's own interpolant of a query over
         bit-vectors and Booleans only, from the executable [./bitwuzla],
         declining when it is absent (off unless listed).
         [unsat] from the CHC solver ends the list with no interpolant.  When
         every leaf declined: no interpolant if a projection was asked for,
         otherwise the failure is reported. *)
  interpolant_post : Interpolation.Interpolant.post list; [@default []]
      (* Steps applied in order to an interpolant a leaf gave, each keeping
         it an interpolant: [Word_regroup o] replaces a group of literals on
         single bits of one argument in a clause by nothing or by an
         equality or disequality of two arguments of that sort, when the
         replacement still separates the two sides (Z3-checked, at most
         [o.max_queries] queries of [o.timeout] milliseconds per
         interpolant).  [[]] keeps the interpolant as it came. *)
  relative_induction_interpolant : int option; [@default None]
      (* Before an interpolant is asked of [interpolant_leaves] for a frame,
         ask for a lemma by relative induction (the clauses of the predicate
         with the frame below and the unknown itself in their bodies, the
         query as goal) and use it, conjoined with the current frame, when the
         clauses are shown to imply that conjunction within this many
         milliseconds.  This changes the question asked, not the procedure
         answering it, so it is a field of its own rather than a leaf.
         [None] asks the leaves only. *)
  counterexample_projections : counterexample_projection list;
      [@default [ Mbp; Model_values ]]
      (* how a counterexample's auxiliary variables are eliminated, in order;
         the first step that returns wins, and the last failure is raised when
         every step declined *)
  projection_conditionals : projection_conditionals; [@default All_paths]
  projection_lets : projection_lets; [@default Inline_lets]
  (* in the bit-vector projection, keep a literal that the slice reading of a left
     shift did not rewrite instead of renormalizing it (the distribution step always
     does so).  The prepass reads the output of the normalization, on which the
     normalization has been observed to return its input unchanged, so this saves its
     cost without, as far as observed, changing the result; the identity is not
     proved, so [false] renormalizes every such literal *)
  bv_reuse_unchanged_prepass : bool; [@default false]
  (* in the bit-vector projection, do not normalize again, at the start of a later step
     of the same projection, a literal that an earlier step returned exactly as its own
     normalization left it (kept by physical identity, within one projection; the
     memo of the normalization across projections is separate and applies to the
     rest).  The normalization has been observed to return nearly all such literals
     unchanged (not all: it is not idempotent on every literal), so this saves its
     cost and, where it is not the identity, leaves an equivalent literal in a form
     the rules may read differently; [false] normalizes every literal at every step *)
  bv_normalize_once : bool; [@default false]
  (* in the projection, when the variable about to be removed is a bit-vector variable
     with a literal x = y or x = c (y a variable, c a numeral), remove every variable
     still to be removed that has such a literal at once: compose the bindings into one
     substitution, apply it to the literals that mention them and normalize each of
     those once.  Each binding is the equivalence (exists x. x = t /\ phi) <-> phi[t/x]
     that the unit-coefficient rule applies one variable at a time, and substitution
     composes, so the literals are those of the one-at-a-time path up to the
     normalization's form; what is saved is renormalizing large literals once per
     binding.  It changes no grammar; [false] leaves every variable to the rules *)
  bv_joint_alias_in_projection : bool; [@default false]
  (* with the [MBP] counterexample strategy, project an implicant of the
     clause body at the countermodel instead of the whole body: every
     conjunct, one true disjunct, with the one-bit circuits first opened into
     Boolean connectives (Spacer projects the implicant of a rule's body at
     its model, after Z3's rewriter has opened them).  The projection then
     sees only the literals of the path the countermodel took, not the
     equalities of the branches it did not take, which the projection would
     otherwise keep or settle by the model's values; [false] projects the
     whole body *)
  mbp_implicant : bool; [@default false]
  (* with [mbp_implicant]: each literal of the implicant also has its
     conditional terms outside binders lifted by the countermodel (the
     condition, or its negation, and the taken branch), as Spacer's implicant
     sees a body whose conditional terms Z3's rewriter has lifted.  The
     projection then works on the branch the countermodel took instead of
     carrying the conditional term into the obligation; [false] keeps each
     conditional term whole *)
  mbp_implicant_lift_ite : bool; [@default false]
  (* with [mbp_implicant_lift_ite] and [mbp_implicant_slice_defs]: the
     implicant is taken with its conditional terms whole, the unused
     definitions of eliminated variables are dropped and the one-bit
     definitions opened, and only then are the conditional terms of the
     remaining literals lifted (and the slice repeated).  Lifting first
     takes the conditions of the conditional terms in every operand of a
     one-bit [or1], where opening it takes one true operand only, and keeps
     the condition of a dropped definition [y = ite c a b] although
     [exists y. y = ite c a b /\ R] is [R] whatever [c] is: the obligation
     then fixes conditions (sign bits of the previous state, say) that the
     kept literals do not need.  Still an implicant; [false] lifts while the
     implicant is taken *)
  mbp_implicant_lift_after_slice : bool; [@default false]
  (* with [mbp_implicant]: the implicant is read off the solver's partial
     assignment rather than off its completion.  Z3's SMT core gives a value
     only to the terms the satisfied formula's Boolean structure needs
     (relevancy), and the model handed to the projection fills the others
     with default values; with this field, where a disjunction has a
     disjunct that holds whatever values those others take, the implicant
     takes it, so the obligation does not depend on the default values.
     Still an implicant at the completed model, so the projection is
     unchanged in kind; [false] takes the first disjunct true at the
     completion *)
  mbp_implicant_partial : bool; [@default false]
  (* with [mbp_implicant]: each [let] variable that a literal of the
     implicant fixes to a bit-vector numeral is replaced by that numeral in
     the other literals before the projection.  Equivalent; it saves the
     projection removing every compound subterm built over such a variable
     one at a time (a one-bit [let] repeated by [concat] into a 128-bit mask
     makes 128 of them); [false] projects the literals as they are *)
  mbp_implicant_fold_lets : bool; [@default false]
  (* with [mbp_implicant]: before one-bit definitions are opened, a literal
     [y = t] is dropped when [y] is a variable the projection eliminates,
     [y] does not occur in [t] and no other literal mentions [y]; repeated
     until none is left.  [exists y. y = t /\ R] is [R] for such [y], so the
     projection is unchanged in meaning.  It keeps the definitions of
     next-state variables the obligation does not constrain from being
     opened, which would fix the current-state bits of their circuits to
     the countermodel's values (a model-based projection removes them by
     substitution instead); [false] keeps every literal *)
  mbp_implicant_slice_defs : bool; [@default false]
  enable_pvar_elim : bool; [@default true]
  check_validity : bool; [@default false]
  proof_search : proof_search; [@default Frame_search]
  (* options for relational verification [CAV'17] *)
  ask_pred_app_to_unfold : bool; [@default false]
  valid_with_smt_threshold : int option; [@default None]
  induct_threshold : int option; [@default None]
  enable_apply_threshold : bool; [@default false]
  normalize_lemma : bool; [@default false]
  check_lemma_lhs : bool; [@default false]
  fold_lemmas : bool; [@default false]
  generalise_goals_by_containment : bool; [@default true]
      (** relational search with user lemmas: for every user lemma of the
          containment shape [K(x~) => W(x~)], each hard goal with a left atom
          on [K] is also tried, after the user lemmas, as a conjecture with
          those atoms on [W] ([Problem.generalise_goals_by_containment]).
          Sound: the renamed goal implies the original once [K <= W] holds in
          the least model, and it is used only when proved.  A goal proved by
          induction on a copy [K] cannot use a lemma about the whole graph [W],
          whose conclusions are [W] atoms the induction hypothesis never
          matches; the renamed goal closes that gap.  On by default: it turned
          relational goals over copies (multiplication commutativity and an
          accumulator variant) from timeouts into answers within 8 s, and it
          adds nothing where no containment lemma exists; a false conjecture
          costs its per-conjecture budget *)
  (* options for QSMT solving *)
  (* what a refutation at the innermost level contributes to the frame two levels out.
     [false] negates the model-based projection of the unsat core, which is a conjunction
     of atoms and, where the core carries a divisibility constraint, describes one
     congruence class at a time.  [true] replaces the refuted player's variables by witness
     terms and instantiates the whole matrix with them, which implies the same refutation
     and keeps the disjunctions of the matrix.  It applies only to the innermost level,
     where every remaining variable belongs to that player and the instance therefore stays
     quantifier-free *)
  subst_lemma : bool; [@default false]
  (* ask each countermodel question of a clause in one Z3 solver that holds the
     clause's constraint part at its root, the rest of the question asserted in
     a push/pop scope, as Spacer asserts a predicate's transition relation once
     in its solver; the question is the same conjunction, so [sat]/[unsat] are
     unchanged and only the model may differ.  An undecided answer is asked
     again the usual way.  [false] converts and asserts the whole question in
     every check *)
  countermodel_body_session : bool; [@default false]
  (* with [countermodel_body_session], keep the Z3 term of every conjunct of
     the rest of a question converted in a clause's session, so that a
     conjunct asked again (a frame lemma of the next trace, asked by most of
     the clause's checks) is not converted again.  Same question, asserted as
     the list of its conjuncts.  [false] converts the whole rest per check *)
  countermodel_session_memo : bool; [@default false]
  (* the simplifier inlines the [let]s of a nest in one pass, deciding each
     before its body and substituting at the leaves, instead of re-simplifying
     the whole body below every inlined [let] (quadratic on a chain of them).
     Meaning-preserving; the simplified formulas can differ in shape and fresh
     names.  Process-wide once on, set when the solver is built; see
     [Ast.Evaluator.simplify_inline_lets_once] *)
  simplify_inline_lets_once : bool; [@default false]
  (* the simplifier does not try to evaluate a bit-vector operation one of
     whose simplified arguments is a variable or another bit-vector operation
     (the attempt fails there, after walking the argument to its leaves:
     quadratic on a nested chain).  Output unchanged.  Process-wide once on,
     set when the solver is built; see
     [Ast.Evaluator.simplify_skip_settled_bv_eval] *)
  simplify_skip_settled_bv_eval : bool; [@default false]
  frames : frames; [@default Common.Util.config_default frames_of_yojson "{}"]
  backtrack_strategy : backtrack_strategy; [@default Deepest_own_variable]
  persistent_frames : persistent_frames option; [@default None]
  qsat_projections : qsat_projection list;
      [@default
        [ Theory_mbp; Read_over_write; Extensionality; Formula_term; Model_value ]]
      (* how the QSMT projection eliminates one non-Boolean variable, in order;
         the first step that returns wins *)
  sampling_estimate : bool; [@default false]
      (* whether a stochastic problem outside the exact solver's prefix shape
         runs the sampling solver ([Sqsat]) to print its estimate on stderr.
         The answer on stdout is [unknown] either way: the estimate is not a
         verdict (see [Solver.solve_smt]).  Off by default because the run
         costs time and memory -- about 1000 Z3 queries per probabilistic
         level, several GB resident -- for a figure no harness reads. *)
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  Or_error.(
    PCSPSolver.Config.load_ext_file cfg.pcsp_solver >>= fun pcsp_solver ->
    (match cfg.muclp_preprocessing with
    | As_converted -> Ok As_converted
    | Optimize { optimizer; rounds } ->
        MuCLP.Optimizer.Config.load_ext_file optimizer >>= fun optimizer ->
        Ok (Optimize { optimizer; rounds }))
    >>= fun muclp_preprocessing ->
    Ok { cfg with pcsp_solver; muclp_preprocessing })

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "MuCyc"
  let instantiate = instantiate_ext_files
end)
