open Core
open Common.Util

type mode =
  | Auto
  | Prove
  | Disprove
  | Parallel of { number_of_pairs : int; [@default 1] }
      (** [number_of_pairs] primal/dual pairs run in parallel domains, no
          information exchanged *)
  | ParallelExc
      (** one primal and one dual run, exchanging learned partial solutions *)
[@@deriving yojson]

(* [dual_witness_refutation]: with [Witness_refutation], in the primal-dual
   exchange every candidate solution the dual sends is read for the values of
   its witness unknowns: an [FN] unknown of the dual whose candidate is a
   constant gives that constant to the binder it skolemises.  The primal
   problem then has every universally read binder replaced by the
   conjunction of its body over a finite value list -- the candidate's
   constant alone for a binder of the query or of a nullary predicate (the
   program's inputs), the constant (if any) and [choice_values] for any
   other integer binder, both truth values for a Boolean one -- and that
   weakened problem is decided by the ground solve with [atom_budget] atoms
   and at most [max_combos] value combinations per binder.  A false
   weakened query refutes the primal: each replacement is implied by the
   binder it replaces and the fixpoints are monotone in their bodies, so
   the answer is [invalid] whatever values were chosen; anything else says
   nothing and the run goes on.  One attempt per distinct set of constants.
   Off by default: it changes which inputs are answered, not what an answer
   means.

   With [Seed_primal_labeling] nothing is decided here: the same constants
   are sent to the primal's constraint solver as seeds (one message per
   distinct set of constants), which holds as examples the ground instances
   of its own clauses that a seeded unfolding from its fact clauses reaches
   -- a variable named after a seeded binder at the binder's constants, every
   other integer variable no premise equation fixes at [choice_values], at
   most [atom_budget] atoms and [max_combos] valuations per matching.  An
   answer, if any, is that solver's own [unsat] from its examples; the seeds
   only choose which instances it holds, so the answer means what any
   primal [invalid] means.  Off by default, and when off no seed is computed,
   sent or read.  [seed_scope] says which of the receiver's phases read the
   instances, [seed_keep] which instances it holds (see both). *)

(* Which phases of the primal's constraint solver read the instances the
   seeds chose.  [Labeling_and_synthesis]: they are ordinary examples, read
   by every phase, template synthesis included.  [Labeling_only]: they, and
   every example derived from them, are held in the example set that
   resolution and labeling read -- so the labeling's refutation, which is
   the only way the seeds can lead to an answer, is unchanged -- but are not
   among the examples template synthesis must satisfy.  Both are sound for
   the same reason: every instance is an instance of one of the receiver's
   own clauses, so a refuted example set refutes the clause set whichever
   phase reads it, and a candidate synthesised without them is still checked
   against the clauses by validation.  [Labeling_only] exists because a few
   thousand consistent instances along a seeded chain constrain every
   synthesis question without helping it. *)
type seed_scope = Labeling_and_synthesis | Labeling_only
[@@deriving yojson]

(* Which of the instances a seed message chose the primal's constraint solver
   holds.  [All_instances]: every one.  [Refutation_cone]: only those a
   labeling refutation of the message's own instances can use -- an instance
   with an atom that occurs with one polarity only and can take that polarity
   freely (an ordinary unknown's atom; a well-founded or parity unknown's atom
   asserted false, or asserted true on an edge no cycle of its family's ground
   graph passes through) is dropped, repeatedly.  The kept set is refuted
   exactly when the message's whole set is: a termination lasso keeps its cycle
   and the stem that forces it, and a chain that closes no cycle is dropped
   whole.  Sound either way, since dropping examples can only lose
   refutations; a refutation that also needs examples held from elsewhere can
   be lost.  It exists because thousands of seeded chain instances that close
   no cycle cost the labeling's propagation and resolution without being able
   to refute anything. *)
type seed_keep = All_instances | Refutation_cone [@@deriving yojson]

type dual_witness_refutation =
  | No_witness_refutation
  | Witness_refutation of {
      atom_budget : int; [@default 20000]
      max_combos : int; [@default 64]
      choice_values : int list; [@default [ 0 ]]
    }
  | Seed_primal_labeling of {
      atom_budget : int; [@default 20000]
      max_combos : int; [@default 64]
      choice_values : int list; [@default [ 0 ]]
      seed_scope : seed_scope; [@default Labeling_and_synthesis]
      seed_keep : seed_keep; [@default All_instances]
      stop_after_fruitless : int option; [@default None]
          (** [Some k]: once [k] consecutive seed messages of one solve kept
              no instance (their unfolding stopped at its budget and was
              declined, or [seed_keep] dropped every instance), the receiver
              unfolds no later message of that solve; a message that keeps
              an instance resets the count.  Sound for any [k]: it only
              holds fewer instances.  Why: on inputs whose seeded chains
              never close (a counter loop), every message ran its unfolding
              to the instance budget and was then declined, 0.5-3.6 s each,
              and the primal's validation spent nearly the whole run on them
              (a valid answer in 0.5 s without seeds took 39-47 s).  [None]:
              every message is unfolded *)
    }
[@@deriving yojson]

(* Partial solutions sent between the primal and the dual run (mode
   [ParallelExc]).  With [Random_examples], the search for partial solutions of
   each predicate of nonzero arity is also given [size] random positive
   examples of it, whose arguments are random terms bounded by [bound]. *)
type extra_partial_sols =
  | No_extra
  | Random_examples of { bound : int; [@default 200] size : int; [@default 0] }
[@@deriving yojson]

(** which variables a fresh unknown of [name_multiplied_parts] takes *)
type name_args =
  | All_free_args
      (** every free variable of the named disjunct and every Boolean
          universal of its clause *)
  | Shared_args
      (** only those the disjunct shares with the other disjuncts of its
          clause: a variable free in it alone is quantified inside the
          definition, which keeps satisfiability both ways
          ([forall y. (A \/ c)] is [A \/ forall y. c] when [y] is not free in
          [A]).  Why: in a transition system's path-composed clauses every
          deeper step's choice variables are free in each enclosing step's
          disjunct, and passing them all gave fresh unknowns of thousands of
          arguments *)
[@@deriving yojson]

(** which disjuncts [name_multiplied_parts] names *)
type name_rule =
  | Fewest_to_bound
      (** the disjuncts of a disjunction over the bound, largest first, until
          the product of the rest is within it *)
  | Gaining_parts
      (** the same, but a disjunct only where naming it shortens the clausal
          form: beside other disjuncts giving [p] clauses, a disjunct of [c]
          clauses is named only when [(p - 1) * (c - 1) > 1]; where no naming
          does, the largest disjunct is distributed over the others as the
          plain clausal form does, and a clause in which nothing is named is
          left as reduced.  One rule for both sides.  Why: on the proving
          side a clause [U(xs) => /\_i (guard_i => successor_i)] has one
          clause beside the conjunction, so naming it saves nothing, and the
          fresh unknown it made stood between the invariant and every
          obligation, turning a two-round refutation into one that did not
          converge *)
[@@deriving yojson]

(** which sides' reductions [name_multiplied_parts] applies to *)
type name_sides =
  | Both_sides
  | Dual_only
      (** only the dual's: the query's negation, whose reduction turns a
          transition system's branching into a disjunction of conjunctions *)
  | Primal_only  (** only the primal's (both primals, with an AD primal) *)
[@@deriving yojson]

(** how a reduction's disjunctions of guarded conjunctions are left *)
type guarded_disjunctions =
  | As_reduced  (** as the reduction writes them *)
  | Factor_exclusive_guards
      (** each group of disjuncts [P_i /\ Y_i] whose pure parts [P_i] are
          pairwise exclusive (a literal of one is syntactically the negation
          of a literal of another, after simplification and normalisation)
          becomes [(P_1 \/ ... \/ P_k) /\ (not P_1 \/ Y_1) /\ ... /\
          (not P_k \/ Y_k)]: equivalent at every valuation, in every model,
          over the same atoms and with no fresh unknown, and its clausal form
          is the sum of the branches' instead of their product.  Why: the
          dual of a transition system's muCLP is at each location a
          disjunction over its outgoing transitions of [guard /\ successor],
          and its distributed clausal form ran to about 2 x 10^10 clauses on
          one 425-location system *)
  | Merge_witnesses_and_factor
      (** before [Factor_exclusive_guards], the copies of one functional
          unknown's witness in a clause, each bound by its own variable, are
          given one variable where the unknown occurs only negatively in the
          problem: equisatisfiable (a functional unknown applied only
          negatively may be read single-valued, and then the copies denote one
          value), but not the same problem.  Why: a transition system's dual
          gives each path through a choice its own copy of the choice's
          witness, so the branches testing it ([x >= 0] on one path, [x' < 0]
          on another) test independent variables, no guard excludes another,
          and the clausal form is their product; with the witnesses shared
          ([qelim.share_witnesses]) and one variable, the guards exclude one
          another and the factoring makes it a sum *)
[@@deriving yojson]

(* Whether the certificate behind a verdict is written after the verdict line
   (the format is [Certificate]'s): never, written as read off the solution,
   or written after Z3 has checked that the invariants form an inductive
   assignment of the problem received (a failed or undecided check withholds
   every invariant and says why).  Writing one makes the side that answers
   keep its solution and the ranking certificates of its well-founded
   unknowns; the verdict, and the questions asked before it, are the same. *)
type print_certificates =
  | No_certificates
  | Unchecked_certificates
  | Checked_certificates
[@@deriving yojson]

(* Where a violation path of an invalid verdict may come from, when
   [print_certificates] asks for the certificate.  Every path is replayed on
   the received problem by ground evaluation before it is written, whatever
   its source, so the choice is about how often a path is found, never about
   whether a written one is right.  [Refutation_only]: only a verdict the
   primal's refutation decided gets a path (the refutation guides the
   search).  [Refutation_and_ground]: also a verdict the ground decision
   ([ground_query_solve]) gave, by the same search without guidance. *)
type violation_sources = Refutation_only | Refutation_and_ground
[@@deriving yojson]

type t = {
  verbose : bool; [@default false]
  output_iteration : bool; [@default true]
  output_yes_no : bool; [@default false]
  output_reduction_stats : bool; [@default false]
      (** print to stderr, for every reduction of a muCLP to a pfwCSP, one line
          counting the parity families, parity relations, ranked predicates,
          ranking functions (a ranked predicate holds one per component of its
          family, each a template that may grow pieces and lexicographic levels)
          and those ranking functions' arguments, summed, and the strongly
          connected components and alternation depth of the problem reduced;
          with [ParallelExc], also one line naming the task whose result ends
          the run *)
  wp_share_choice : bool; [@default true]
      (** when a transition system is converted to a muCLP, whether a choice
          whose postcondition is large keeps that postcondition shared between
          its branches (an equivalent, not identical, muCLP whose size no longer
          doubles per choice) instead of copying it into each branch; the
          environment variable [COAR_WP_SHARE_CHOICE] overrides it for
          debugging ([0] off, any other value on) *)
  wp_share_choice_min_size : int; [@default 256]
      (** the size above which a choice is shared: a choice is shared only
          when its postcondition has more than this many formula nodes; read
          only when [wp_share_choice] is on *)
  lts_cut_point_choice : LTS.Problem.cut_point_choice;
      [@default LTS.Problem.Graph_order]
      (** which of the location sets that meet every cycle of a transition
          system's control-flow graph its termination encoding takes as the
          least-fixpoint (ranked) locations: [Graph_order] breaks the ties of
          the greedy choice by the graph's hash order (so by the location
          names), [Loop_heads] by the loop structure (the back-edge targets of
          a depth-first search from the start, independent of the names).
          Every such set gives an encoding with the same solution, so this
          moves which ranking functions are searched for, never a verdict *)
  t2_division : LTS.Problem.division; [@default LTS.Problem.Exact]
      (** how a T2 file with a [BUCHI] line (the dialect of LTL-VerP,
          Chatterjee et al., FM 2024) reads [/]: [Exact] as exact division by
          a constant over integer variables (guards scaled by the
          denominators, an assignment of a non-integer value has no
          successor), [Truncate] as T2's truncating integer division,
          [Refuse] refuses such a file when it divides.  A T2 file without a
          [BUCHI] line always truncates.  Read by the reader, before any
          solving *)
  (* validity checking for muCLP *)
  optimizer : MuCLP.Optimizer.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/muclp/optimizer/enable.json"]
  second_round_growth_limit : float option; [@default None]
      (** [ParallelExc] optimizes the problem a second time before splitting
          it into the primal and the dual; with [Some f] the second round's
          result is kept only when its formula nodes are at most [f] times its
          input's, and otherwise its input is used.  The round's inlining can
          compose large bodies whose clausal forms are products: one transition
          system grew from 13 predicates to 8 and 8.6 times in size, and its
          primal then could not build its clause set within the memory cap,
          where the once-optimized problem's took a fraction of a second.
          [None] keeps the round's result always (default). *)
  task : mode; [@default ParallelExc]
      (** what is proved: the query, its negation, both in parallel, or both
          exchanging partial solutions *)
  fixpoint_reduction : MuCLP.Reducer.Config.fixpoint_reduction; [@default MuCLP.Reducer.Config.Wf_reduction { restrict_ranking_to_cycles = true; record_on_head = false; one_relation_per_block = false }]
      (** how the least fixpoints become well-foundedness constraints; the
          alternation depth and the packing of rank components exist only in the
          parity progress measure *)
  guarded_disjunctions : guarded_disjunctions; [@default As_reduced]
      (** see [guarded_disjunctions]; applied to both sides' reductions,
          before [name_multiplied_parts] *)
  name_multiplied_parts : int option; [@default None]
      (** [Some n]: in the constraint problem a reduction produces, every
          clause whose clausal form is predicted to have more than [n] clauses
          has the conjunctions its disjunctions multiply named by fresh
          ordinary unknowns ([D(xs)] in place of [C], and [D(xs) => C] beside
          it), which preprocessing never eliminates.  Sound both ways in every
          model: the problem with the fresh unknowns is satisfiable iff the
          original is, and its solutions restricted to the original unknowns
          are the original's, so verdicts and the partial solutions exchanged
          between the two sides keep their meaning; the solver has the fresh
          unknowns to find besides.  Why: the dual of a transition system's
          muCLP is a disjunction over branches of conjunctions, whose clausal
          form is the product of theirs (one dual clause of 22,835 nodes had
          about 2 x 10^10 clauses), and every pass that builds the clausal
          form never finished.  [None]: the clauses are left as reduced *)
  name_args : name_args; [@default All_free_args]
      (** with [name_multiplied_parts]: the fresh unknowns' arguments *)
  name_rule : name_rule; [@default Fewest_to_bound]
      (** with [name_multiplied_parts]: which disjuncts are named *)
  name_sides : name_sides; [@default Both_sides]
      (** with [name_multiplied_parts]: the sides whose reductions name; a
          side left out is reduced as with [None].  Sound in every choice,
          since each side's problem alone is equisatisfiable with its
          unnamed form and its solutions restricted to the original unknowns
          are that form's, so the exchanged partial solutions keep their
          meaning *)
  alternation_depth_primal : bool; [@default false]
      (** with [task = ParallelExc] and a parity-progress-measure reduction
          that holds [alternation_depth] and [loop_levels], also run a second
          primal, in a third domain, whose every parity family keeps
          alternation depth's priorities for the whole search (Kura and Unno,
          Def. 7.7-7.8), beside the primal reduced with the loop-hierarchy
          priorities.  The loop levels give a nested loop a ranking component
          per level from the start, which the search otherwise grows one
          failure at a time; alternation depth's single component can be
          refuted in fewer rounds where the query is invalid, and a refutation
          found under either reduction refutes the other (on a component with
          no greatest fixpoint a cycle is rejected under one priority function
          exactly when under the other).  The second primal takes part in the
          exchange like the first: the dual's partial solutions are sent to
          both, and its own to the dual.  It answers at once, and is ignored,
          when no family's two priority functions differ; any answer of it but
          valid or invalid is ignored too, so the run then waits for the other
          two.  Ignored with any other task or reduction.  Costs a third
          solving domain on the inputs where the priorities differ. *)
  qelim : MuCLP.Qelim.Config.t; [@default Common.Util.config_default MuCLP.Qelim.Config.of_yojson "{}"]
  output_certificates : string option; [@default None]
      (** a file to which each solved side writes the solution of every
          predicate named [U_state_<location>_], C-style, one per line: the
          transition-system route's old exit, kept for its users *)
  print_certificates : print_certificates; [@default No_certificates]
      (** write the certificate of the side that decided the verdict after
          the verdict line (see [print_certificates]) *)
  violation_sources : violation_sources; [@default Refutation_only]
      (** which invalid verdicts get a violation path (see
          [violation_sources]); read only with [print_certificates] *)
  extra_partial_sols : extra_partial_sols; [@default No_extra]
  ground_query_solve : MuCLP.GroundSolve.Config.t;
      [@default MuCLP.GroundSolve.Config.default]
      (** whether a ground query is decided before the reduction
          ([MuCLP.GroundSolve.run], which states the class, the budget and
          what an answer guarantees); the default is every muCLP engine's,
          on.  It decides answers without the reduction and without
          constraint solving, so a configuration that is to run a paper's
          reduction method states [No_ground_solve]. *)
  dual_witness_refutation : dual_witness_refutation;
      [@default No_witness_refutation]
      (** whether each candidate the dual's constraint solver sends fixes the
          primal's universally read binders to the values it gives, and the
          rest is decided by a ground solve, refuting the primal when the
          instance is false (see [dual_witness_refutation]) *)
  send_lower_bounds : bool; [@default false]
  pcsp_solver_primal : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/pcsat_muval.json"]
  pcsp_solver_dual : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/pcsat_muval.json"]
  qfl : QflConfig.t; [@default Common.Util.config_default QflConfig.of_yojson "{}"]
      (** the quantitative solver's own fields (validity checking for
          Quantitative Fixpoint Logic); the muCLP solver reads none of them *)
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  Or_error.(
    PCSPSolver.Config.load_ext_file cfg.pcsp_solver_primal
    >>= fun pcsp_solver_primal ->
    PCSPSolver.Config.load_ext_file cfg.pcsp_solver_dual
    >>= fun pcsp_solver_dual ->
    MuCLP.Optimizer.Config.load_ext_file cfg.optimizer >>= fun optimizer ->
    MuCLP.Qelim.Config.instantiate_ext_files cfg.qelim >>= fun qelim ->
    Ok { cfg with pcsp_solver_primal; pcsp_solver_dual; optimizer; qelim })

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "MuVal"
  let instantiate = instantiate_ext_files
end)
