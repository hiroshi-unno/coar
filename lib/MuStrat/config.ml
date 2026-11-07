open Core
open Common.Util

(** How the budget of the strategy check (one CHC query per turn) grows when a
    query times out, and which side checks next.  A timeout is never a verdict
    under either policy: both only decide which check runs next and with what
    budget, and every answer still comes from a check that returned. *)
type chc_timeout_policy =
  | Global_doubling
      (** One budget shared by both sides (and one for the backup solver).  A
          timed-out check is retried on the same side with the budget doubled,
          and the budget is never reset, so a check the backend cannot decide
          holds the run: the turn never passes, and every later check of either
          side starts from the inflated budget. *)
  | Pass_turn_on_timeout
      (** Each side keeps its own budget (and its own backup budget).  A
          timed-out check doubles the budget of the side that timed out and
          passes the turn to the other side, exactly as an [unknown] from the
          backup solver already does; the timed-out side is checked again, with
          the doubled budget, when the turn comes back.  So one side's hard
          check delays the other side by at most its current budget instead of
          starving it. *)
[@@deriving yojson]

(** The arithmetic of the LP ranking candidate's linear questions (the
    Farkas conditions over its multipliers, coefficients and constants). *)
type lex_candidate_arith =
  | Integer
      (** Every unknown an integer: each question is an integer linear
          program, decided by Z3's branch and bound. *)
  | Rational_unbounded
      (** The questions without a coefficient bound (the single first
          question and the unbounded construction) ask every unknown as a
          real, a linear program over the rationals decided by simplex, and
          each component found is scaled by the least common multiple of its
          denominators to integer coefficients.  Without a bound on the
          coefficients or the constant every such question is satisfiable
          exactly when its integer form is (an integer solution is a rational
          one, and scaling a rational one by a positive integer keeps every
          constraint, the decrease [<= -1] becoming [<= -L <= -1]), so the
          construction takes the same steps; the scaled components keep every
          condition they were asked for.  The unit-coefficient construction
          stays an integer program: a bound on rational coefficients before
          scaling is a different restriction. *)
[@@deriving yojson]

(** The rungs on a component's constant that the LP ranking candidate asks
    before leaving the constant free ([chain_pair_lex_candidate_const_ladder],
    read only with [chain_pair_lex_candidate_const_first = Some b]).  Every
    rung is a preference: a question is asked under a rung only when the
    tighter rungs before it found no component, and without any rung last, so
    the questions decided, and hence whether a candidate is found, are those
    of the construction without the rungs; only which components are found
    changes. *)
type lex_candidate_const_ladder =
  | Fixed_rung
      (** One rung, [|c| <= b], on the unit-coefficient construction only:
          the behaviour of [chain_pair_lex_candidate_const_first] alone. *)
  | Literal_rung
      (** Two rungs on the unit-coefficient construction: [|c| <= b], then
          [|c| <= M] with [M] the largest absolute integer literal of the
          game (skipped when [M <= b]).  A constant within the game's
          literals is one a guard of the game can state (a loop bound
          [8 - i]); a constant beyond every literal can only come from the
          values the plays happened to take. *)
  | Literal_rung_everywhere
      (** The two rungs of [Literal_rung] on every construction of the
          candidate that asks [RankingCheck.lex_ranking] (the
          unit-coefficient one, the unbounded ones and the small-first
          bounds), not only the unit-coefficient one.  In the rational
          form a rung bounds the constant before scaling, relative to the
          decrease of 1 the strict conditions ask. *)
[@@deriving yojson]

(** The bound [B] on the opponent's free choices ([bounded_counterplay]). *)
type counterplay_bound =
  | Largest_literal
      (** [B] is the largest absolute value [M] of an integer literal in the
          checked side's problem (at least 1).  The literals cut the integers
          into the cells of the atoms [v < c], [v = c], [v > c]; every cell
          meets [-M..M] except the two outer ones, [v > M] and [v < -M].  So
          the bound keeps a representative of every way a choice compared
          directly with the literals can go, and excludes only the plays
          whose choice lies beyond every literal -- such as a play entering
          the branch past a capacity guard [x > 2^30], whose refinement then
          offers a constant beyond it. *)
  | Fixed of int  (** [B] is the given value (at least 0). *)
[@@deriving yojson]

(** Whether a strategy check's counter-play is sought with the opponent's free
    choices bounded ([bounded_counterplay]).  The opponent's free choices are
    the results of its Skolem keys, which the check leaves unconstrained (each
    key [F] enters the checked side's problem as the goal [not F(a, r)], one
    fact of the Horn clauses).  The bounded check restricts each such fact to
    [-B <= r <= B]: every clause of it is implied by the corresponding clause
    of the check, so a derivation of its query (a counter-play) is a
    derivation of the check's query, made of the same steps.  It decides
    nothing by being satisfiable: a win under the bound may rest on a value
    beyond it, so only the check itself can be won, and no verdict is read
    from the bounded check under any constructor. *)
type bounded_counterplay =
  | No_bound  (** The check is asked as it is, and nothing else. *)
  | Bounded_first of counterplay_bound
      (** The bounded check is asked before the check, once per strategies
          of a side; its counter-play is read as the check's, anything else
          is discarded and the check is asked.  It changes the counter-play
          read whenever one exists under the bound, so it moves runs whose
          plays never leave the bound as well. *)
  | Reask_beyond of counterplay_bound
      (** The check is asked as it is; only when its counter-play plays a
          free choice of the opponent with absolute value above [B] is the
          bounded check asked, and its counter-play, if it returns one,
          replaces the check's.  A run whose plays stay within the bound is
          the run without the field. *)
  | Reask_isolated_outlier of counterplay_bound
      (** As [Reask_beyond], but the bounded check is asked only when one
          free choice alone takes the counter-play beyond [B]: a choice of
          absolute value above [B] that also exceeds the absolute value of
          every integer of the state at which it is made (the other
          arguments of the opponent's key), that state having at least one.
          A choice made from small states past a large capacity guard
          triggers it; the starting positions of a game whose positions are
          compared with each other (keys with no state argument) do not.
          Only which counter-play is read changes, never a verdict, as for
          [Reask_beyond]; a run in which no such choice is played is the run
          without the field. *)
[@@deriving yojson]

(** Whether the strategy loop offers the members of a fixed hypothesis space
    besides what the refinement proposes ([relative_completeness]). *)
type relative_completeness_mode =
  | Rc_off  (** Only the refinement proposes terms and rankings. *)
  | Unbounded
      (** Every term of the space (integer terms with literal multiples and
          division by literals; real affine terms) is offered to each side's
          Skolem keys, one vector per offer, layer by layer, and every
          ranking-function relation of the space is tried for the side's
          ranking keys in a check of its own (a probe), each infinitely
          often; two stalls in a row no longer answer [unknown].  So if a
          side has a winning strategy in the space, the run ends with that
          side's answer, given that every check asked is eventually decided;
          on an input with no such strategy it runs until stopped. *)
  | Capped of int
      (** The same with the offers and probes confined to the layers up to
          the given one; the run answers [unknown] once both sides have been
          offered every term of those layers and every ranking of them has
          been probed and lost after that, which then means that no side has
          a winning strategy in that finite space. *)
[@@deriving yojson]

(** Under [demonic_fallback_on_undecided_check]: whether a restricted copy's
    satisfiable check is read as a win of the ordinary check, and where in a
    timed-out check's handling the copies are asked.  The handling tries, in
    order, the ground split, the two re-asks (when on), the copy-blind
    re-check and the copies, then passes the turn or retries.  Reading a
    copy's win is sound wherever it is asked: the copy's check is the check
    of a single-term strategy of the same side with the same rankings, and
    its win enters the ordinary check's win rules (a ranking neither recorded
    by construction nor proved transitive still needs the copy-blind check of
    the side's whole strategy).  The steps before it read only their own
    check, so moving the copies changes which question is asked first, not
    what any answer rests on. *)
type demonic_copy_wins =
  | Not_read
      (** A copy's win is discarded; the copies are asked last and only
          propose the opponent's candidates from their counter-plays. *)
  | Read_after_copy_blind
      (** A copy's win is read; the copies are asked last, after the
          copy-blind re-check returned neither a win nor a counter-play. *)
  | Read_before_copy_blind
      (** A copy's win is read; the copies are asked after the ground split
          and the re-asks and before the copy-blind re-check, whose encoding
          alone can take seconds on a large check.  When no copy decides,
          the copy-blind re-check follows as without the field.  Not before
          the ground split: with its default of no extra solver question the
          split costs no Z3 time, while the copies cost up to their count
          times their budget. *)
[@@deriving yojson]

(** What a won strategy check needs before it is an answer when Z3 does not
    prove every ranking the checked side substitutes transitive.  A ranking is
    a finite union of well-founded pieces, hence disjunctively well-founded,
    and a transitive disjunctively well-founded relation is well-founded
    (Ramsey's theorem), so a win whose rankings are proved transitive is an
    answer under every constructor.  With a ranking that is only
    disjunctively well-founded, the reduced check can be won by choices that
    read the remembered copy of an earlier state, and an invalid query was
    answered [valid] that way; a win of the copy-blind encoding
    ([copy_blind_choices]) does not rest on such choices.  Accepting an
    ordinary check's win under neither condition is unsound, so it has no
    constructor.  A win that is not an answer passes the turn with both
    strategies unchanged, and two such or stalled turns in a row answer
    [unknown]. *)
type untransitive_win =
  | Recheck_copy_blind
      (** The same strategies are checked once more with
          [copy_blind_choices]'s encoding, and that check decides: a win there
          is an answer, a counter-play there refines the opponent.  A win of a
          check that already was copy-blind is an answer.  The default. *)
  | Inconclusive
      (** The win is not an answer, whether the check was ordinary or
          copy-blind: only a win whose rankings are proved transitive is. *)
  | Recheck_copy_blind_then_inconclusive
      (** An ordinary check's win is re-checked as under
          [Recheck_copy_blind]; a copy-blind check's win is not an answer, as
          under [Inconclusive]. *)
[@@deriving yojson]

(** Whether a won ordinary (not copy-blind) check whose rankings are not
    proved transitive is checked again copy-blind before anything is
    decided. *)
let rechecks_copy_blind = function
  | Recheck_copy_blind | Recheck_copy_blind_then_inconclusive -> true
  | Inconclusive -> false

(** Whether a won check whose rankings are not proved transitive, and that
    is not re-checked, is inconclusive rather than an answer; [copy_blind] says
    whether the won check was copy-blind.  Never [false] for an ordinary check
    under a mode that does not re-check it, so no such win is an answer. *)
let untransitive_win_inconclusive ~copy_blind = function
  | Recheck_copy_blind -> false
  | Inconclusive -> true
  | Recheck_copy_blind_then_inconclusive -> copy_blind

(** How a refinement problem's Skolem terms are found.
    [Terms_pcsat]: every refinement goes to [pcsp_solver].
    [Terms_select]: when a refinement problem is a pure existential over its
    Skolem unknowns -- every unknown of kind [FN], each universal defined by a
    nullary Skolem constant, and the opponent's key copies applied only
    positively, each unknown once -- it is solved from one Z3 model by
    model-guided term selection (Farzan and Kincaid, IJCAI 2016) instead of
    calling [pcsp_solver], and the result is checked valid before it is used.
    Any other problem, or a selection whose check fails, still goes to
    [pcsp_solver].  The refined strategy is checked by the same strategy check
    either way, so the choice changes which strategies are proposed and never
    how an answer is decided.  Its two options are independent:
    - [mentioned_only]: before a refinement is tried by selection, the
      unknowns no formula of the problem mentions are removed from its
      signature, so the selection's tests (every unknown of kind [FN], one
      theory sort) read only the unknowns the problem constrains.  A ranking
      copy that the build solved itself (an offered linear-programming
      candidate) stays declared and is mentioned by no constraint; without
      the option it made the selection refuse the whole problem as "an
      unknown not of kind FN", and the mixed-sort Skolem keys went to the
      constraint solver with it.  Exact: the formulas are the same, the
      selection answers only with a solution it checks valid on every
      formula, and the copies it does not solve are filled in afterwards by
      the build's own solutions; an unknown nobody mentions and nobody solved
      is left as it was.
    - [split_mixed]: a refinement problem whose unknowns are Skolem keys
      ([FN]) together with ranking copies ([WF]/[DWF]) is not a pure
      existential, so selection does not apply to it and the constraint
      solver solves the whole problem, returning one template term per
      Skolem copy (a copy-blind counter-play's refinement added 13 to 19
      terms for one key this way, where selection added one to four).  With
      this on, such a problem is split into the formulas that mention a
      ranking copy and the rest, provided the two share no unknown; the rest
      is solved by selection and the ranking part by the constraint solver,
      and the two solutions are joined.  Sharing no unknown, a solution of
      each part is a solution of the whole; when selection does not apply to
      the rest, or the ranking part is not solved, the whole problem goes to
      the constraint solver. *)
type refine_terms =
  | Terms_pcsat
  | Terms_select of {
      mentioned_only : bool; [@default false]
      split_mixed : bool; [@default false]
    }
[@@deriving yojson]

let selects_terms = function Terms_select _ -> true | Terms_pcsat -> false

(** How the terms selected for the copies of one opponent key are combined;
    read only under [Terms_select].  The copies each get their own function
    from the selection, and each is added to that key's term set.
    [Unguarded]: the ungrouped solution is used.
    [Separation]: the copies whose selected terms differ are combined into one
    guarded definition [ite(g_1, t_1, ite(g_2, t_2, .. t_m))], the guards
    separating the argument points at which each term was selected (a
    threshold on one parameter where one exists, else a linear separator from
    a small Z3 query); copies whose terms agree share one branch.  The
    combined definition replaces the copies' functions only when the problem,
    with it substituted for every copy, passes the same validity check as the
    ungrouped solution; otherwise, or when a group's points cannot be
    separated (two copies selected at one argument point with different
    terms), the ungrouped solution is used unchanged.  The strategy check is
    unchanged, so this changes which strategy is proposed and never how an
    answer is decided.
    [Cav24_sound]: before the copies are combined as under [Separation], the
    term each copy takes is re-decided by the determinization of Murphy and
    Kincaid (CAV 2024, Section 6): the copies whose key has two or more
    selected terms are ordered into a chain, each offered every term of its
    key (evaluated at its argument point); the losing relations of that
    chain -- one per depth, over the values chosen above it, holding where
    every remaining choice loses the play -- are solved by the engine
    [refine_labels] names, and each copy takes the first term in a fixed
    preference order (terms over the parameters before constants, then
    terms selected by more copies) whose choice the solution does not
    declare losing.  Any solution of that system makes the chosen values a
    winning choice of the play, so the copies then combine as under
    [Separation] -- one term for a key whose copies all chose it, otherwise
    the separation guards -- with the same validity check.  When the
    system has more than [Cav24Guards.max_branches] term combinations, when
    the engine gives no solution, or when a copy's argument point or a
    term's value cannot be read, the selection's own terms are combined as
    under [Separation]. *)
type refine_guards = Unguarded | Separation | Cav24_sound [@@deriving yojson]

(** The engine that solves the losing relations of [refine_guards =
    Cav24_sound]; read only there.  [Labels_forward]: forward propagation
    over the recursion-free system, the least solution (each relation the
    exact set of positions where every remaining choice loses), computed by
    substitution.  [Labels_spacer]: the CHC solver of
    [refine_labels_spacer_solver] (Spacer by default), whose solution may be
    any one, so a term can be declared losing where it does not lose.
    [Labels_regions]: forward propagation decides the copies' values as under
    [Labels_forward]; then every copy takes the most preferred term with its
    value (also when no copy had two values to choose from), and a key whose
    copies still play two or more terms gets guards read off the play
    symbolically instead of separation's: each copy's label region is the
    model-based projection, onto the key's parameters around the copy's
    point, of the weakened refinement formula with every copy's result
    equated to its term at its own arguments; a term is guarded by the
    disjunction of its copies' regions.  The decision list is installed only
    when it gives every copy its value at its own point and the problem with
    it passes the validity check; otherwise that key is combined by
    separation as under [Labels_forward]. *)
type refine_labels = Labels_forward | Labels_spacer | Labels_regions
[@@deriving yojson]

(** Which reading of a counter-play the refinement's term selection is asked
    on; read only under [Terms_select].
    [Ground]: the refinement problem built from the play with every value of
    the checked side inlined is the only reading.  A key of the refuted side
    whose argument is the opponent's earlier move then sees that move as a
    constant, and the selection can only return a constant: on
    [forall x. exists y. 2y <= x <= 2y + 1] each refinement added one guarded
    constant for the one [x] the opponent played, and no refinement ever
    proposed [y = x div 2].
    [Lifted]: on a counter-play read from the check with the checked side's
    strategy values kept as defined predicates
    ([chain_pair_regions_free_opponent_values]), the selection is first
    asked on the play with each value that the check fixed to a ground
    constant kept as a variable: the tag predicate is not resolved away, its
    constant enters only the model the selection reads, and its solution in
    the returned answer is its definition again.  This is the
    counter-strategy synthesis of Farzan and Kincaid (IJCAI 2016,
    Algorithm 2): a term is selected from the condition of the subtree below
    the move, with the earlier moves free and their values in the model.
    The answer is used only when it is checked valid on the play with the
    values pinned, which is the refinement problem itself, so it beats the
    same play; otherwise the refinement proceeds as under [Ground].  It
    answers [valid] on the game above.
    [Lifted_free_goal]: as [Lifted], with the two things that can still make
    the lifted play ground removed.  A key of the checked side that the play
    mentions only in its query (a clause with no head) is not tagged, so its
    values are inlined; and the goal instance at the root of the derivation
    carries the ground values the CHC backend chose, so resolving the
    derivation onto it writes them back into every key argument.  With the
    universals of a game named as keys both hold on
    [forall x. exists y. x = y]: every refinement asked [y] for one more
    ground [x] and the game never ended, where the constraint solver's
    refinement returns [y = x] at once.  Here such query-only keys are tagged
    as well (which changes the shape of the re-asked check, not its answer),
    and the goal instance's ground arguments become universally quantified
    variables, so the opponent's values are held only by the tags (pinned in
    the selection's model) and the refuted side's own values stay free -- the
    premise of Farzan and Kincaid's selection (Section 4.1), whose formula
    keeps the earlier moves free -- and a key whose result is a term over
    its arguments is selected through the equality atom that states it.  The
    answer is used only when, with every other unknown solved, it is checked
    valid on the ordinary refinement problem.  It answers the game above in
    about 1.5 s.
    All three change which strategy is proposed, never how an answer is
    decided: the refined strategy goes through the same strategy check.  The
    default is [Lifted_free_goal]: on the games where no checked-side value
    is a single ground fact the lifted selection is either not asked or
    gives nothing, and the refinement is the one [Ground] makes.  The code
    reads the field only through [lifts_play] (either lifted reading) and
    [frees_goal] (the generalised goal). *)
type refine_counter_play = Ground | Lifted | Lifted_free_goal
[@@deriving yojson]

let lifts_play = function Ground -> false | Lifted | Lifted_free_goal -> true
let frees_goal = function Lifted_free_goal -> true | Ground | Lifted -> false

(** How the ranking part of a refinement is found, relative to the terms.
    [Separate]: the chain pairs of the counter-play are read off the play
    with the opponent's decisions named, and each ranking key gets a fresh
    copy constrained by those pairs, solved independently of how the Skolem
    terms are chosen; the ranking fields (regions, the linear-programming
    candidate's depth, re-synthesis, the forms tried on failure) are its
    parameters.
    [Joint_guided]: as [Separate] to find the ranking, but when the ranking
    of every ranking copy is fixed before the terms are chosen (a candidate
    the refinement built itself, by linear programming or from
    certificates), the terms are selected so that the play's chain pairs
    decrease under that ranking with the ranked side moving by them.  The
    states at the ranked predicate's visits are kept as terms of the
    counter-play's clauses, the decrease of every chain pair under the fixed
    ranking is conjoined to the formula the terms are selected from, and the
    selection starts from a model at the counter-play's own visit states
    when one exists.  Model-guided selection preserves the formula it
    selects from (Farzan and Kincaid, IJCAI 2016, Lemmas 4.3 and 4.4), so at
    the model the selection ends at, the play of the counter-play's skeleton
    with the ranked side moving by the selected terms ends where it ended
    and decreases on every chain pair.  A term that fits the play only by
    staying where the ranking needs a step down (the move [y := x] beside
    the ranking [x]) is thereby never selected.  When the selection does not
    apply (no ranking fixed beforehand, an unknown that is not a Skolem
    key, a formula outside linear arithmetic, no model) the refinement is
    the [Separate] one.  Read only with [refine_terms = Terms_select].
    [Joint_steered k]: as [Joint_guided], with three differences.  (1) The
    terms are selected on the counter-play's own clauses only (the goal at
    the query's values, the checked side's values inlined), never on a
    lifted or goal-generalised form of them: only a model of the check's own
    clauses is a play of the check, and on a formula with the goal
    generalised a ranking met at another goal instance can be installed
    beside terms that lose from the real one.  (2) Each joint answer records,
    besides the played pairs, the chain pairs of the play at the model the
    selection started from and at the model it ended at (where the ranked
    side moves by the selected terms) into the pairs every later ranking of
    the key must contain, so a later re-synthesised ranking still ranks the
    play the installed terms make.  (3) When the refinement fails because no
    ranking contains the played pairs, the refinement is steered: up to [k]
    other resolutions of the counter-play's own clauses are asked (each
    pairing no visit with an equal state, none at the state vector of the
    played one or of a resolution already tried), a ranking is built for
    each over the pairs every accepted refinement has asked of the key and
    that resolution's own, and the first for which the joint selection
    succeeds is installed with its terms, its own pairs recorded and the
    played pairs not.  [k] bounds the work of one refinement (at most [k]
    resolution questions, ranking constructions and selections), not
    progress.  Read only with [refine_terms = Terms_select] and
    [resynthesise_wf_rankings].
    Every value only proposes the next strategy, which is checked like any
    other, so none changes how an answer is decided. *)
type refine_rankings = Separate | Joint_guided | Joint_steered of int
[@@deriving yojson]

(* whether the ranking of a refinement is fixed before its terms are
   selected (so a single linear ranking is offered as a candidate) *)
let ranking_fixed_first = function
  | Separate -> false
  | Joint_guided | Joint_steered _ -> true

(** The ordered list of interpolation procedures a guard built from tree
    interpolants would ask, each tried in turn, a procedure that declines
    passing the query to the next (the leaves of [Interpolation.Interpolant]).
    No refinement reads it yet: the guards built from interpolants are not
    built, so the loader accepts only the default [[Farkas_lra; Spacer_chc]]
    (a Farkas refutation over the rationals first, an integer-only
    infeasibility, which has no such refutation, passed to the CHC solver)
    and refuses any other list rather than ignore it. *)
let default_refine_interpolant_leaves =
  Interpolation.Interpolant.[ Farkas_lra; Spacer_chc ]

type t = {
  optimizer : MuCLP.Optimizer.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/muclp/optimizer/enable_erase_query.json"]
  ground_query_solve : MuCLP.GroundSolve.Config.t;
      [@default MuCLP.GroundSolve.Config.default]
      (** whether a ground query is decided before the strategy loop
          ([MuCLP.GroundSolve.run], which states the class, the budget and
          what an answer guarantees), on the optimizer's output; the default
          is every muCLP engine's, on.  An answer it gives comes from neither
          the reduction nor a strategy check, so a configuration that is to
          run the strategy loop only states [No_ground_solve]. *)
  wp_share_choice : bool; [@default true]
      (** when a transition system is converted to a muCLP, whether a choice
          whose postcondition is large keeps that postcondition shared between
          its branches (an equivalent muCLP whose size no longer doubles per
          choice) instead of copying it into each branch; MuVal's field of the
          same name.  The shared form is equivalent, so it changes the problem
          this solver is given but never its answer.  Without it a transition
          system with many successive choices converts to a problem
          exponential in their number, and the conversion alone can exhaust
          the memory or the budget: on three such termination inputs the
          conversion took 278 to 299 s copied and under 5 s shared.  On by
          default since it was measured together with
          [counter_plays_per_check] at 1 and [resynthesise_only_on_new_pairs]
          on (and the strategy check's Spacer with its concretize step off):
          on 1,424 termination and muCLP inputs at 300 s, four runs of every
          input whose answer differed, the three together answered 7 inputs
          the previous defaults did not and lost none, no two runs gave
          opposite verdicts, and the inputs both answered took 0.89 of the
          time in sum (median ratio 0.94).  Off, every choice copies its
          postcondition, as before the field existed. *)
  wp_share_choice_min_size : int; [@default 1024]
      (** the size above which a choice is shared (formula nodes of its
          postcondition); read only when [wp_share_choice] is on.  1024 here,
          where MuVal's is 256, because the shared form costs this solver
          more than it costs MuVal: it binds the disagreeing next-state
          values as fresh universal variables tied to the state by a
          disjunction of equalities, and this solver reads every universal of
          a least-fixpoint body as an opponent decision.  The dual side must
          then synthesise those determined values as Skolem functions, and
          the chain regions read from its counter-plays fix the state at the
          plays' values, so the ranking candidates memorise constants
          ([c - x] for growing [c]) where the copied form gives a ranking
          over the state ([n - x]).  Three inputs whose shared
          postconditions are 256 to 1024 nodes lost their answers that way;
          at 1024 their conversion is the copying one, while the inputs whose
          conversion is exponential without sharing share postconditions far
          above 1024 and still convert in seconds and answer. *)
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
  chc_solver : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/gspacer_cex.json"]
      (** The CHC solver that decides a strategy check.  Every MuStrat
          configuration shipped under [config/solver] states it, and those
          that use Spacer with global guidance name
          [gspacer_cex_noconc.json]: global guidance with its concretize step
          off.  That is a workaround for a defect of Z3 5.1.0's Spacer, not a
          search preference: when a blocking check of a proof obligation comes
          back undecided, Spacer treats the obligation as not blocked with no
          model set and the concretize step then evaluates a literal in that
          null model, killing the process with a segmentation fault.  It was
          adopted together with [wp_share_choice], [counter_plays_per_check]
          at 1 and [resynthesise_only_on_new_pairs] (7 inputs gained, none
          lost, on 1,424 inputs at 300 s).  Re-examine it when Z3 changes
          version.  The code default here is the plain configuration, which
          other users of the field's file share. *)
  backup_chc_solver : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/spacer_cex.json"]
  pcsp_solver : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/pcsat_mustrat.json"]
  pcsp_solver_determ : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/strat_synth_determ_forward.json"]
  refine_preprocessor : Preprocessing.Preprocessor.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/preprocessor/mustrat_refine.json"]
      (** The preprocessor the strategy refinement runs on a counter-play's
          clauses to eliminate the auxiliary unknowns while keeping the
          strategy unknowns, whose solutions it reads back (an elimination,
          never a satisfiability question: the refuting stages do not run).
          It is not the preprocessor of [pcsp_solver], which decides the
          refinement problem built afterwards.  The default file asks for an
          unbounded resolution threshold, four boolean arguments eliminated
          and no argument reduction, every other field at its default. *)
  determinize : bool; [@default false]
  lra_virtual_terms : bool; [@default false]
      (** Play the real strategy game of [-p smt] with Loos-Weispfenning
          virtual terms (a strict bound plus or minus an infinitesimal,
          checked and exported as the midpoint of the two bounds) instead of
          the default selection (the nearer bound, or that bound stepped into
          the interval by a unit fraction computed from the model).  Both are
          sound; the default answered more of the SMT-LIB quantified LRA
          files at 10 s. *)
  clausal_reductions : bool; [@default false]
      (** Put the primal and the dual reduction's constraint problems in
          negation and conjunctive normal form before solving.  The two forms
          are equivalent, so this changes the shape the backends and the
          refinement see, not the problem (the conversion is not among the
          rewrites [validate_verdicts] records); off, the reductions are passed
          as they are built, which is how every shipped configuration has
          run. *)
  check_problem : bool; [@default false]
  output_yes_no : bool; [@default false]
  name_opponent_decisions : bool; [@default true]
      (** Make the checked side's derivation mention the opponent's decision
          points, so that the refinement can find them, and adapt the
          alternation to refinements that can now fail without the checked side
          losing: each universal of the checked side becomes a dummy predicate
          named as the opponent's Skolem key (fixed to false, which keeps the
          check exact), the refinement reads the pairs a ranking must cover off
          the derivation's play, and a refinement that fails or changes nothing
          passes the turn instead of answering [invalid].  The greatest-fixpoint
          predicates are reduced without a remembered-state encoding whatever
          this says, and a checked side with an empty strategy is refuted by a
          counter-play whatever this says.

          This is the umbrella: each of the four behaviours below has its own
          field, and a field left at [None] follows this one.  So a config that
          states none of them means exactly what it meant before they existed,
          and a measurement can switch one behaviour while holding the others. *)
  name_universals : bool option; [@default None]
      (** Skolemise the checked side's universals into dummy predicates named as
          the opponent's Skolem keys ([conv_forall] of the existential
          elimination), so that a derivation mentions the opponent's decision
          points.  [None] follows [name_opponent_decisions]. *)
  chain_pairs_from_play : bool option; [@default None]
      (** Read the counterexample derivation as a ground play tree and give each
          of the opponent's ranking keys a fresh copy constrained, as facts, by
          the pairs of states its ranking must cover: pairs of visits to the
          ranked predicate along a path, with the chain reset at a visit to a
          predicate earlier in the equation list.  Without it no such copies
          are added.  Meaningful only when the derivation is a complete play,
          i.e. with [name_universals] on.  [None] follows
          [name_opponent_decisions]. *)
  splice_chain_revisits : bool; [@default false]
      (** Before the chain pairs are read, cut every revisit out of the play:
          when a visit to a ranked predicate at state [s] has, below it and
          with no reset in between, another visit at the same [s], the upper
          visit's subtree is replaced by the lowest such visit's.  A ranking
          contains no pair [(s, s)], and a revisit with a visit at [t] in
          between asks it for both [(s, t)] and [(t, s)], which no
          well-founded relation contains; with the cut the opponent is asked
          to rank only the play it makes by taking, at a repeated state, the
          move of its last visit there.  The pairs asked are a subset of those
          asked without the field, so every refinement found without it still
          solves the refinement asked with it.  Off, the pairs [(s, s)] are
          dropped and the rest of the cycle is asked for, as before the field
          existed.  Nothing here decides an answer: the strategy check does. *)
  resynthesise_wf_rankings : bool; [@default true]
      (** Refine a ranking key by replacing its ranking with ONE relation of
          kind [WF] that contains every chain pair any accepted refinement of
          the key has asked for, instead of disjoining a new [DWF] piece onto
          it.  The ranking template's instances are well-founded whatever
          their parameters, so a ranking obtained this way is well-founded,
          and a win whose rankings are all of this kind or proved transitive
          is accepted without the copy-blind re-check (a won check with
          well-founded rankings is sound even when a choice reads the
          remembered copy).  A key whose accumulated pairs contain a cycle has
          no well-founded relation containing them, so it is refined as
          without the field; and when the attempt does not succeed within the
          check's current budget, the refinement is asked again exactly as it
          is with the field off.  Only keys whose copies are constrained by
          chain-pair facts alone take part.  On by default: on the POPL 2024
          games and ten smaller inputs it lost no answer and gave one the
          guarded union could not, an invalid input on which the union's
          check is won only by choices that read the copy.  Off, every
          refinement disjoins, as before the field existed. *)
  resynthesise_only_on_new_pairs : bool; [@default true]
      (** Read only with [resynthesise_wf_rankings].  An accepted refinement
          changes a ranking key's ranking (by replacement or by a disjoined
          piece) only when the chain pairs the refinement asked of that key
          include one the current ranking does not contain, the test being
          ground evaluation of the ranking at each pair; otherwise the ranking
          is kept as it is, while the pairs are still recorded as asked.  A key
          whose refinement asked no chain pair (its copies come from the
          derivation) is refined as without the field.  With it, a key's
          ranking changes only because a pair outside it was asked, and every
          later ranking of that key contains that pair, so a key's rankings
          never repeat; within a finite space of terms and rankings the
          alternation of refinements then stops, with an answer or [unknown].
          Without it, a refinement asking only pairs already covered can
          return another ranking on the same facts (the constraint solver's
          answer depends on fresh names), and two sides can revisit earlier
          rankings forever.  An undecided evaluation counts as a pair not
          contained, which lets the ranking change as without the field.  The
          field adds no answer rule.  On by default: measured with
          [wp_share_choice] on and [counter_plays_per_check] at 1 on 1,424
          termination and muCLP inputs at 300 s, the three together answered
          7 inputs the previous defaults did not and lost none, with no two
          runs giving opposite verdicts and 0.89 of the time on the inputs
          both answered; the same two settings without this field lost one
          input the previous defaults answered in every run (answering it in
          one run of four); with this field it was answered in the one run
          made.  Off, a key's ranking may change on pairs it already
          contains, as before the field existed. *)
  generalise_chain_pairs : bool; [@default true]
      (** Read only with [resynthesise_wf_rankings].  Before a ranking key is
          re-synthesised as one [WF] relation, each chain pair (s, t) the plays
          ask of it is also stated as a region: the clause instances of the
          derivation along the path from the visit at s to the visit at t are
          conjoined, the side premises dropped except that the result of each
          of the ranked side's named decisions is fixed at the value the play
          took, and the conjunction is projected onto the two visits' states
          by model-based projection at the play's values.  The copy is asked
          to contain every such region as well as every ground pair, so the
          fit is made on the steps a play of that shape takes rather than on
          the points it happened to visit.  Each region contains its ground
          pair (the projection is taken at a model assigning the play's
          values, and a region the ground pair does not satisfy is discarded),
          so a solution of the generalised problem solves the ground one.
          When no region can be formed, or the generalised problem is not
          solved within the check's budget, the refinement is asked exactly as
          without the field.  The field adds no answer rule, and a solution is
          a template instance, hence well-founded however it was fitted.  Off,
          only the ground pairs are asked, as before the field existed. *)
  chain_pair_regions_with_passed_choices : bool; [@default true]
      (** Read only with [generalise_chain_pairs].  Each chain-pair region is
          formed with, at every node of its path segment, the conditions under
          which the alternatives the ranked side passed over there cannot win
          (from the clauses of the check that returned the play: the negation
          of the alternative clause's pure body, its premises read as
          derivable wherever one of their clauses' pure bodies holds, after
          quantifier elimination), each kept only where it holds at the play's
          values.  A step the ranked side takes by its own choice carries no
          clause guard; this restores where taking it is right.  The
          conditions only narrow a region, so every region still contains its
          ground pair and the demand on the ranking only weakens; an answer
          still comes from a won strategy check.  Off, the regions are formed
          as before the field existed.  Also read with
          [chain_pair_regions_by_mbp], which then adds the conditions only at
          the visits of the ranked predicate (never at a node naming one of
          the checked side's term alternatives, whose clause bodies hold that
          side's strategy constants). *)
  passed_choices_at_ranked_visits_only : bool; [@default false]
      (** Read only with [generalise_chain_pairs] and
          [chain_pair_regions_with_passed_choices].  The passed-over
          alternatives' losing conditions are taken only at the nodes of a
          segment that visit the ranked predicate, never at its auxiliary
          nodes, among them the ones naming the checked side's term
          alternatives: their clause bodies hold that side's strategy
          constants, and conditions read there cut a region into slices
          bounded by those constants, which can leave the region problem
          unsolved within its budget.  Soundness is unchanged: a condition
          still only narrows a region, and dropping some only widens the
          narrowed region back towards the unnarrowed one, so every region
          still contains its ground pair and an answer still comes from a won
          strategy check.  Off, conditions are taken at every node but a
          segment's last. *)
  chain_pair_regions_by_mbp : bool; [@default true]
      (** Read only with [resynthesise_wf_rankings]; usable alone or with
          [generalise_chain_pairs], which it then replaces (the regions are
          formed as below, never as that field forms them).  Each chain pair
          (s, t) is stated as the region obtained by model-based projection
          of the segment's whole derivation: the clause instances along the
          path from the visit at s to the visit at t AND the instances of
          every side premise's derivation below the path (so the checked
          side's strategy, substituted into the check, is kept rather than
          dropped), each of the ranked side's named decisions fixed at the
          value the play took, projected onto the two visits' states at the
          model the play gives (every node's ground arguments).  So every
          pair of a region is joined by a derivation fragment of the check
          under the play's decisions: the region under-approximates the
          realisable steps instead of over-approximating them, and still
          contains its ground pair.  A side derivation larger than a fixed
          node budget is dropped as [generalise_chain_pairs] drops every side
          premise.  Regions are deduplicated after renaming their variables
          to one canonical list per key, and a ground pair some region of the
          problem contains is not asked separately (the region clause implies
          it, so the problem is unchanged).  When projection declines or
          raises, the pair is asked as a ground fact.  The field adds no
          answer rule; a solution is a [WF] template instance.  Off, as
          before the field existed. *)
  chain_pair_regions_by_mbp_problem_sides_only : bool; [@default true]
      (** Read only with [chain_pair_regions_by_mbp].  A side premise whose
          node is not a predicate of the problem (a term alternative's name,
          a Skolem dummy) is dropped from the derivation that is projected,
          as [generalise_chain_pairs] drops every side premise: such a
          node's clause body holds the checked side's strategy constants,
          and kept, they bound each region at the play's values, so the
          regions grow in number round by round while each covers less.
          Soundness is unchanged: dropping a premise only widens the region
          towards the one without side derivations, which still contains its
          ground pair, and an answer still comes from a won strategy check;
          the under-approximation of realisable steps is then given up for
          the dropped premises.  Off, every side derivation within the node
          budget is kept. *)
  chain_pair_regions_free_opponent_values : bool; [@default true]
      (** Read only with [name_term_alternatives], and of use only with the
          regions of [generalise_chain_pairs] or [chain_pair_regions_by_mbp].
          When a check is built, each term of the checked side's Skolem keys
          is replaced by a fresh predicate defined by that term, wherever the
          key occurs only as a negated premise literal, so that the value the
          key decides stays a variable of the clause instead of being inlined
          as the strategy's constant; the check is unchanged up to these
          definitions.  A chain-pair region then drops the defining premise,
          so it holds the steps of its derivation shape under every value of
          the opponent's move instead of the one the play took.  Dropping a
          conjunct only widens a region, which still contains its ground
          pair, and an answer still comes from a won strategy check; a
          widened region with no linear ranking is dropped like any other.
          Off, the strategy is substituted as before the field existed. *)
  freed_reask_timeout : int option; [@default None]
      (** Read only with [chain_pair_regions_free_opponent_values].  A cap, in
          seconds (the unit of every check budget; at least 1), on the budget
          of the tagged re-ask asked after a lost check.  [None] asks it at
          the check's budget capped at [chc_initial_timeout].  The verdict is
          always the ordinary check's, so the cap changes only which
          counter-play the refinement reads: a re-ask cut short leaves the
          ordinary one. *)
  bounded_counterplay : bounded_counterplay; [@default No_bound]
      (** Unless [No_bound], a counter-play is also sought in the check with
          the opponent's free choices bounded ([bounded_counterplay] gives when).
          Asked only on a side's ordinary check (not a copy-blind check or
          re-check, nor a re-check after a timeout), when the checked side has
          a strategy and the opponent has a Skolem key in the check, at the
          check's budget capped at [chc_initial_timeout].  A counter-play it
          returns is read as the check's (the extra plays, the tagged re-ask
          and the refinement then read the bounded clauses, whose regions also
          hold the bound); anything else is discarded.  Exact for every
          answer: no verdict is read from the bounded check, so the field
          changes only which counter-play the refinement reads, at the cost of
          one bounded question when it is asked and finds none. *)
  isolated_outlier_factor : int; [@default 1]
      (** Read only with [bounded_counterplay = Reask_isolated_outlier _].  A
          free choice [r] made at a state whose largest absolute value is [m]
          is an isolated outlier when [r > f * m] for this factor [f] (values
          below 1 read as 1).  With 1, a choice one past a small bound and
          one past its state (a counter's next value) triggers the bounded
          re-ask; with 2 the choice must more than double every value of its
          state, as a choice crossing a large capacity guard from a small
          state does.  Changes only whether the bounded check is asked,
          never a verdict. *)
  freed_reask_skip_after_failures : int option; [@default Some 1]
      (** Read only with [chain_pair_regions_free_opponent_values].  With
          [Some n], a side whose last [n] tagged re-asks in a row returned no
          counter-play is not re-asked again in the run (a re-ask that returns
          one resets the count, but none follows once the side is skipped).
          [None] re-asks after every lost check.  Exact for the verdict, as
          [freed_reask_timeout] is. *)
  chain_pair_region_multiphase_depth : int; [@default 2]
      (** Read only with [resynthesise_wf_rankings] and the regions of
          [generalise_chain_pairs] or [chain_pair_regions_by_mbp].  A region
          with no linear ranking is dropped; with this above 1, such a region
          is first asked for a nested (multiphase) ranking of depth 2 up to
          this value, and kept with that ranking as its certificate when one
          exists.  When a key's regions then hold a certificate, the
          certificates are tried as candidate rankings, the one from the
          shortest chain segment first: the first whose single-piece
          lexicographic order contains every region of the key (each proved
          by Z3) and every ground pair asked of it (each by evaluation) is
          the key's ranking, and the key's copy is not handed to the
          constraint solver.  When none is accepted, the regions holding a
          certificate are dropped and the problem is exactly the one asked
          with the field at 1.  Soundness is unchanged: the candidate is an
          instance of the ranking template (one piece, a trivially true
          discriminator), well-founded for any coefficients, and an answer
          still comes only from a won strategy check.  At 1 (or below), as
          before the field existed. *)
  chain_pair_lex_candidate_depth : int; [@default 3]
      (** Read only with [resynthesise_wf_rankings].  When a ranking key's
          copy is re-synthesised as one well-founded relation (over its
          regions, or over its ground chain pairs alone) and no multiphase
          candidate is accepted, a candidate built by linear programming
          over all the key's regions without a multiphase certificate and
          all its ground pairs is tried first: a lexicographic linear
          ranking of depth 2 up to this value, built greedily level by level,
          and, when the construction finds none at any depth up to this
          value, a ranking of two pieces split at a threshold on an integer
          position that every region fixes to a constant.  Nothing is
          offered when one linear function ranks everything, since that is
          the constraint solver's own first shape.  The first candidate whose order
          contains every such region (each proved by Z3) and every ground
          pair asked of the key (each by evaluation) is the key's ranking,
          and the copy is not handed to the constraint solver.  Soundness is
          unchanged: either candidate is an instance of the ranking template
          (one piece with lexicographic components, or two pieces with one
          component each and affine discriminators), well-founded for any
          coefficients, and an answer still comes only from a won strategy
          check.  At 0 (or below), as before the field existed; at 1, only
          the two-piece candidate, where no linear ranking exists. *)
  chain_pair_region_window : int; [@default 1]
      (** Read only with the regions of [generalise_chain_pairs] or
          [chain_pair_regions_by_mbp].  Above 0, a chain pair becomes a
          region only when its lower visit is among the nearest this many
          earlier visits of the segment whose state differs from its own;
          every other pair is still asked as a ground fact.  The number of
          regions (one model-based projection each) is then linear in a
          play's length instead of quadratic.  A ranking template instance
          is transitive, so one that contains the regions of nearby visits
          contains their compositions, but the region of a long segment is a
          projection at the play's point that the composition of its
          sub-segments' regions need not contain: the demand is weaker, and
          what it can lose is a generalisation, never soundness, since an
          answer still comes from a won strategy check.  At 0 (or below),
          every pair becomes a region, as before the field existed. *)
  chain_pair_segments_window_key : bool; [@default true]
      (** Read only with [chain_pair_region_window] above 0 and the regions of
          [generalise_chain_pairs] or [chain_pair_regions_by_mbp].  The walk
          that reads each chain pair's path segment off a play visits a
          shared node once per distinct list of the segment's earlier states
          met at it; on, once per distinct shortest prefix of that list
          (nearest first) holding one more distinct state than the window.
          The segments and pairs are the same, since what a subtree pairs is
          decided by that prefix; only the walk's work changes, so on by
          default.  Off, the whole list, as before the field existed: on a
          play whose shared nodes are reached along many paths the walk then
          visits each node once per path, and did not finish in 290 s on plays
          of a few hundred visits.  The refinement sees the same pairs either
          way, so a strategy the opponent was refined against is still never
          proposed again. *)
  chain_pair_region_drop_implied : bool; [@default false]
      (** Read only with the regions of [generalise_chain_pairs] or
          [chain_pair_regions_by_mbp].  Before a region is stated or offered,
          each of its conjuncts that the region's other remaining conjuncts
          imply is dropped, in order, each implication decided by one Z3
          validity question with a short budget (a question whose shape may
          not return is not asked, and an undecided conjunct is kept).  The
          region is the same set of pairs, so the refinement problem is the
          same problem; only the constraint solver's qualifiers and the
          linear programs' rows shrink.  A projection of a derivation segment
          conjoins the side guards of every step and repeats many of them in
          weaker forms: on a warehouse game a region of 68 conjuncts was the
          set of 7 of them, the constraint solver's hypothesis space built
          from the 68 (511 qualifiers) answered nothing in 40 s, and from the
          7 (44 qualifiers) answered in 1.7 s.  Off, the projection is stated
          as it comes. *)
  chain_pair_region_window_min_pairs : int; [@default 0]
      (** Read only with [chain_pair_region_window] above 0.  Above 0, the
          window is applied to a play only when the play asks more than this
          many distinct chain pairs of the key (counted without the window);
          a play asking at most this many has every pair made a region, as
          with the window off.  The window exists for long plays, whose
          regions are quadratic in their length; on a short one it saves
          little and drops the long segments' regions, which can be the
          demand that steers the fitted ranking.  Soundness is unchanged
          either way: an answer still comes only from a won strategy check.
          At 0 (or below), the window applies to every play. *)
  chain_pair_transitive_reduction : bool; [@default true]
      (** Read only with [resynthesise_wf_rankings].  When a ranking key's
          copy is re-synthesised as one well-founded relation, its ground
          chain pairs (stored and new) are replaced by their transitive
          reduction before they are stated as facts, offered to the
          candidates built by linear programming and checked against them.
          Every instance of the ranking template is transitive, and so is
          every candidate (each is an instance), so a solution contains the
          reduction exactly when it contains every pair: the problem's
          solutions are unchanged and only the number of facts falls (from
          quadratic to about linear in a play's length).  The stored pairs
          and the per-refinement record keep every pair.  Off, every pair is
          asked. *)
  chain_pairs_nearest_visits_only : bool; [@default true]
      (** The chain pairs a refinement asks of a ranking key are read off
          the play with each visit of the ranked predicate paired only with
          the nearest earlier visit of its segment, instead of with every
          earlier one.  The pairs read have the same transitive closure as
          the full set, so where a ranking key's copy is re-synthesised as
          one well-founded relation (acyclic pairs, with
          [chain_pair_transitive_reduction]) its facts, the cycle test and
          every transitive ranking's containing them are unchanged: there
          the option is exact and changes only how long the search takes.
          What does change: the pairs recorded per key for later
          refinements and the facts of a copy that is not so re-synthesised
          (cyclic pairs, a copy in the derivation, [resynthesise_wf_rankings]
          off) are the nearest ones, which a non-transitive copy may satisfy
          without the rest; that alters the search, never the meaning of an
          answer, since an answer still comes only from a won strategy
          check.  On by default because a play that runs a loop thousands
          of times along one path makes the full set quadratic in the
          number of visits (millions of pairs): building and sorting it
          took the whole time budget.  With the nearest pairs a long play's
          peak memory fell from 9.3 GB to under 0.5 GB, two inputs answered
          two to four times faster, and a ten-input comparison lost no
          answer and gained one.  Off, every pair is read. *)
  chain_pair_lex_candidate_const_first : int option; [@default None]
      (** Read only with [chain_pair_lex_candidate_depth] above 0.  [Some b]:
          the unit-coefficient construction of the candidate asks each of its
          linear questions first with the component's constant within
          [-b, b], and without that bound only when the bounded question
          finds no component.  The questions decided are the same, so only
          which components are found changes.  A region read from a play is
          often bounded on a position only because the play's path took a
          branch bounding it, and the unbounded question can then answer a
          component whose constant is that bound ([33 - j] where [acc - j]
          ranks the same regions); the candidate then fails on the first
          play beyond the bound, which a strategy check may need dozens of
          steps to reach and time out looking for.  Soundness is that of
          [chain_pair_lex_candidate_depth]: whatever the components, the
          candidate is a template instance and an answer still comes only
          from a won strategy check.  [None], as before the field existed;
          MuStrat's entry configuration ([config/solver/mustrat.json], with
          the muCLP optimizer's one-point elimination) states [Some 1], and
          the code default is kept at [None] so that the configurations
          derived from the earlier entry load as they did.
          [chain_pair_lex_candidate_const_ladder] says which rungs follow
          [b] and on which constructions. *)
  chain_pair_lex_candidate_const_ladder : lex_candidate_const_ladder;
      [@default Fixed_rung]
      (** Read only with [chain_pair_lex_candidate_const_first = Some b]:
          the rungs asked on a component's constant before it is left free,
          and on which constructions (see [lex_candidate_const_ladder]).
          [Fixed_rung], the meaning [Some b] had before this field. *)
  chain_pair_lex_candidate_linear : bool; [@default false]
      (** Read only with [chain_pair_lex_candidate_depth] above 0.  When one
          linear function ranks every region and pair the candidate is built
          from, offer it too (its order is the one-piece template instance
          with one component), instead of leaving the key to the constraint
          solver, which fits the same demands by its own search and may
          choose a ranking that generalises less.  Off, nothing is offered
          then.  Soundness is that of [chain_pair_lex_candidate_depth]. *)
  chain_pair_lex_candidate_dedup_rows : bool; [@default false]
      (** Read only with [chain_pair_lex_candidate_depth] above 0.  The linear
          programs of the candidate read each region's (and ground pair's)
          rows once per distinct list of rows rather than once per region.
          Rows are positional, so the regions of one loop step read at many
          points of a long play are often equal lists; duplicates add the
          same constraints, and the greedy pass that ranks regions one at a
          time ranks the same lists with or without them, up to questions
          undecided in their budget and the model returned.  Off, one linear
          program per region at each level, as before the field existed. *)
  chain_pair_lex_candidate_skip_covered_pairs : bool; [@default true]
      (** Read only with [chain_pair_lex_candidate_depth] above 0.  Build the
          candidate from the regions and only those ground pairs no region
          holds at, rather than from every pair.  A pair a region holds at is
          a point of that region, so a component that ranks the region ranks
          the pair and a component that does not increase on it does not
          increase on the pair: the linear questions about the remaining rows
          imply the left-out ones.  The greedy construction can still choose
          differently, since it adds rows one at a time.  Each row is one
          question per level, so the pairs dominate the cost when a play is
          long: 206 pairs beside 3 regions spent over 60 s in the
          construction, where the 3 regions alone take one question per
          level.  The candidate is checked against every region and pair as
          before.  Off, every pair is read. *)
  chain_pair_lex_candidate_linear_above : int option; [@default Some 3]
      (** Read only with [chain_pair_lex_candidate_depth] above 0, and only
          when [chain_pair_lex_candidate_linear] is off.  [Some b]: when one
          linear function ranks every region and pair the candidate is built
          from and the construction without a coefficient bound finds it with
          coefficients whose absolute values sum to more than [b], or a
          constant of absolute value above [b], offer it, as
          [chain_pair_lex_candidate_linear] would.  The constraint solver's
          ranking template starts from coefficient sum 1 and constant 0 and
          grows each bound by one per failure up to a threshold (3 in the
          shipped template) before lifting it, so a ranking past that is one
          the solver reaches, if at all, only after its bounds are gone.
          Whether this fires depends on the model the unbounded question
          returns, which has no objective: on a warehouse game it answered
          coefficients 1024 and about 4.7e13 where [2 * energy] ranks every
          region, so a large model says nothing about the demand (with
          [chain_pair_lex_candidate_small_first] the small bounds are asked
          first and the test reads their answer).  A linear ranking within
          [b] is still left to the solver.
          [None]: nothing is offered then.  Soundness is that of
          [chain_pair_lex_candidate_depth]: the offered order is a template
          instance, well-founded whatever its coefficients. *)
  chain_pair_lex_candidate_small_first : bool; [@default false]
      (** Read only with [chain_pair_lex_candidate_depth] above 0.  Where the
          construction would ask its questions without a coefficient bound
          (after the unit-coefficient construction has offered nothing), ask
          the construction with every coefficient within [-b, b] for [b] = 1,
          2, 3 first, as integer programs, and take the first that finds
          components; only when none does, the unbounded construction as
          before.  The unbounded question asks feasibility with no objective,
          so the magnitude of its model is the solver's choice: on a warehouse
          game it answered coefficients in the tens of thousands where
          [2 * energy] ranks every region.  The bounded questions make the
          offered ranking's magnitude a property of the demand, and the
          ranking the one the constraint solver's template, which grows its
          bounds from 1, would reach first.  Every later test on the
          components ([chain_pair_lex_candidate_linear_above], whether a
          single function is offered) reads the components found this way.
          Soundness is that of [chain_pair_lex_candidate_depth]: whatever the
          components, the offered order is a template instance, well-founded,
          and offered only when it is proved to contain every region and
          pair.  Off, the unbounded construction directly. *)
  chain_pair_lex_candidate_single_first : bool; [@default false]
      (** Read only with [chain_pair_lex_candidate_depth] above 0.  Ask first
          the one linear question without a coefficient bound: is there a
          single affine function ranking every region and pair read?  When
          there is one and it would not be offered (neither
          [chain_pair_lex_candidate_linear] nor
          [chain_pair_lex_candidate_linear_above] selects it), no candidate is
          built and the key goes to the constraint solver, whose own first
          shape is that ranking; the constructions after it are not asked.
          Otherwise the constructions run as without the field, the
          unbounded one skipping the question just asked.  The one change in
          what is offered: where a single linear ranking within the
          template's reach exists, a lexicographic candidate the
          unit-coefficient construction would have found is no longer
          offered.  That construction is the expensive part: one question
          per region per level, and on a warehouse game it took about 10 s
          per ranking key over 40 ground pairs, ending in the single ranking
          [-2 x6 + 3] that is then left to the solver anyway.  The questions
          it skips also draw fresh names, so the rest of the run follows a
          different trajectory: on a robot game the default answers, the
          field answered on one of three builds differing only in where fresh
          names start, the default on two.  With
          [chain_pair_lex_candidate_direct_points] the skipped construction
          is cheap anyway.  Soundness is that of
          [chain_pair_lex_candidate_depth]. *)
  chain_pair_lex_candidate_memo : bool; [@default true]
      (** Read only with [chain_pair_lex_candidate_depth] above 0.  Keep the
          outcome of the candidate built over a key's ground pairs alone (no
          region), keyed by the key, its parameters and the pairs, and give it
          again when the same candidate is asked again in the run, instead of
          building it anew.  The construction reads nothing else, so the
          outcome is the one a rebuild would compute from the same questions
          (a solver's model may differ between asks, and either model's
          candidate is checked against every pair before it is kept).  The
          same build happened twice per refinement whenever the attempt over
          the regions found no region (it builds the candidate, adds no region
          clause, and the attempt over the pairs builds it again), and again
          in the next refinement asked the same pairs.  Off, every ask
          builds. *)
  chain_pair_lex_candidate_direct_points : bool; [@default true]
      (** Read only with [chain_pair_lex_candidate_depth] above 0.  In the
          linear questions of the candidate's constructions, a region that is
          one integer point (a ground chain pair, read as the region of its
          equalities) states each implication about it as one inequality over
          the unknown coefficients, its value at the point, instead of through
          Farkas multipliers.  The two have the same solutions in the
          coefficients (for an integer point, integer multipliers prove an
          integer inequality exactly when it holds at the point), so every
          question has the answer it had; only a solver's choice of model may
          differ.  The multipliers made each pair cost [4 n] fresh unknowns and
          [2 n + 1] equations per implication over [n] state positions: a
          warehouse game's questions over 40 pairs took 0.44 s each, most of
          it converting and asserting the formula rather than solving it.  A
          region that is not one integer point is asked as before.  Off, every
          region goes through the multipliers. *)
  chain_pair_lex_candidate_arith : lex_candidate_arith;
      [@default Rational_unbounded]
      (** Read only with [chain_pair_lex_candidate_depth] above 0.  The
          arithmetic of the candidate's questions without a coefficient bound
          ([lex_candidate_arith]).  [Integer] asks them as integer programs;
          [Rational_unbounded], the default, asks them as linear programs over the
          rationals, which decides the same questions (the same answers, the
          same regions ranked at each level, up to a question left undecided
          within its budget and read as "no") and only the model, so the
          components, may differ.  One unbounded question on a warehouse game
          needing a very large coefficient took 7.15 s as an integer program
          and 0.026 s as a linear program.  Soundness is that of
          [chain_pair_lex_candidate_depth]: whatever components are found,
          the offered order is a template instance and is checked against
          every region and pair. *)
  chain_pair_lex_candidate_base_session : bool; [@default false]
      (** Read only with [chain_pair_lex_candidate_depth] above 0.  Ask each
          level of each construction's search in one Z3 solver of its own
          that holds the level's common part -- the coefficient bounds and
          every remaining region's non-increase -- converted and asserted
          once; each question then converts and asserts only its strict
          conditions, in a scope.  Without it every question converts and
          asserts all of it again: a level over 29 regions asks 29 questions
          that each restate the 29 regions' non-increase.  The questions are
          the same conjunctions, so their answers are Z3's answers to the
          same questions; only the solver they are asked in (incremental),
          and so the models and what is decided within a question's budget,
          can differ.  A base the session refuses is asked as before.
          Soundness is that of [chain_pair_lex_candidate_depth]. *)
  chain_pair_lex_candidate_conjunct_memo : bool; [@default true]
      (** Read only with [chain_pair_lex_candidate_depth] above 0.  Ask the
          candidate's linear questions under [Z3interface.with_conjunct_memo]:
          the rows a question shares with the previous one (a level's
          non-increase rows) keep their Z3 terms instead of being converted
          again, and each question reaches Z3 as one n-ary conjunction
          instead of a left-nested binary one, which Z3's assertion flattens
          in time quadratic in its length.  Z3 is given the same question
          (the argument is at [Z3interface.with_conjunct_memo]), so the
          answers are Z3's answers to the same questions, asked in the same
          pooled solver.  Soundness is that of
          [chain_pair_lex_candidate_depth]. *)
  chain_pair_lex_candidate_sign_cells : bool; [@default false]
      (** Read only with [chain_pair_lex_candidate_depth] above 0.  When
          neither the lexicographic nor the two-piece construction gives a
          candidate, try a piecewise ranking whose pieces are the sign cells
          of one or two discriminators read off the regions' own rows
          ([RankingCheck.sign_cell_ranking]): one affine component per cell,
          found by one linear query per split.  A Manhattan distance to a
          target, which splits on two signs, is such a ranking.  The
          questions follow [chain_pair_lex_candidate_arith].  Soundness is
          that of [chain_pair_lex_candidate_depth]: whatever the query
          answers, the offered order is [template_order_pieces] on the cells,
          which is well-founded, and it is offered only when it is proved to
          contain every region and pair. *)
  chain_pair_lex_candidate_sign_cells_prune : bool; [@default false]
      (** Read only with [chain_pair_lex_candidate_sign_cells].  Drop from the
          sign-cell query every (earlier cell, later cell) combination of a
          region that is empty because the state would have to cross a
          discriminator's threshold in a direction the region never moves it
          (one feasibility question per region and discriminator and
          direction).  Without it such a combination still gets its demand,
          which Farkas' lemma may fail to certify for an empty set when the
          demand's coefficients are not in the span of the region's rows, so
          a ranking that exists is lost; with it the query asks the same of
          every non-empty piece and is smaller.  Soundness is that of
          [chain_pair_lex_candidate_sign_cells]: the offered order is still
          checked to contain every region and pair. *)
  bound_last_refinement : bool; [@default false]
      (** Ask the last form of a ranking refinement -- the one with disjoined
          [DWF] pieces, reached when the re-synthesis attempts over the
          regions and over the ground pairs have not succeeded, together with
          every refinement that declares no [WF] copy at all (a pure Skolem
          one) and the retry with the first play alone -- under the same
          budget as those attempts (the check's current budget) instead of
          none.  A refinement whose demands no ranking of the template class
          meets (a union of regions holding an infinite chain) otherwise
          does not return, and the loop stalls inside it.  An expired budget
          is the constraint solver's [Timeout], and it is not read as a
          failed refinement: the side's check budget is doubled and the turn
          passes, with the count of failed refinements in a row (two of which
          answer [unknown]) left as it is, so only a refinement that returned
          unsolved or unchanged counts toward it.  The budget holds only when
          the constraint solver lets the timer through (PCSat's synthesis
          query re-raises it).  No answer rule changes: an
          answer still comes only from a won check.  Off, the last form is
          asked with no budget. *)
  first_play_wf_resynthesis : bool; [@default true]
      (** Read with [resynthesise_wf_rankings].  When the ranking
          re-synthesis attempts over all the counter-plays of a check (over
          their regions, then over their ground chain pairs) do not succeed,
          the same two attempts are asked again over the first play alone,
          before the refinement with disjoined [DWF] pieces over all the plays.
          The further plays are found by blocking the first play's exits, so
          they can take moves of the ranked side the first play did not take
          (on a side whose choices are left to its ranking, any move the check
          left open); their pairs together can admit no ranking at all, and
          then every attempt that reads them fails although the first play's
          pairs alone have one.  Off, the first play alone is asked only in
          the disjoined form, after the disjoined form over all the plays,
          which is not bounded unless [bound_last_refinement] is set.  The
          attempts added are bounded as the other re-synthesis attempts are;
          no answer rule changes. *)
  refine_terms : refine_terms;
      [@default Terms_select { mentioned_only = false; split_mixed = false }]
      (** See [refine_terms]. *)
  refine_guards : refine_guards; [@default Separation]
      (** Read only under [Terms_select]; see [refine_guards]. *)
  refine_labels : refine_labels; [@default Labels_forward]
      (** Read only under [refine_guards = Cav24_sound]; see
          [refine_labels]. *)
  refine_labels_spacer_solver : PCSPSolver.Config.t ext_file;
      [@default Common.Util.ExtFile.Filename "./config/solver/spacer_sol.json"]
      (** The CHC solver of [refine_labels = Labels_spacer]; loaded only when
          [refine_guards = Cav24_sound] and [refine_labels = Labels_spacer],
          and read only there. *)
  refine_counter_play : refine_counter_play; [@default Lifted_free_goal]
      (** See [refine_counter_play]. *)
  refine_rankings : refine_rankings; [@default Separate]
      (** See [refine_rankings]. *)
  refine_interpolant_leaves : Interpolation.Interpolant.leaf list;
      [@default default_refine_interpolant_leaves]
      (** See [default_refine_interpolant_leaves]. *)
  select_skolem_mixed_sorts : bool; [@default true]
      (** Read only with [refine_terms = Terms_select].  A pure-existential refinement
          whose universals and keys are integers and reals together, which the
          one-sort selections decline, is solved by constants read off one Z3
          model of the weakened formula (every Skolem constant its model value,
          every key the constant function of its result's value), used only
          when every formula with them substituted checks valid; otherwise it
          goes to the constraint solver as without the field.  One such
          refinement of a warehouse game (integer task counters, a real energy)
          sent the constraint solver a problem it did not answer in 98 s.  It
          only proposes the opponent's terms, so no answer rule is added.  Off,
          such a refinement always goes to the constraint solver. *)
  select_initial_atom_rows : bool; [@default false]
      (** Read only where [select_skolem_mixed_sorts] answers a refinement.
          Besides the one model's constants, offer more initial values of the
          keys with no argument (the side's choice of an initial state): for
          each atom of the refinement's weakened formula that mentions only
          those keys' results, one more model in which it takes the other
          truth value than in the first model (equations made true first),
          every other key kept at its first value, used only
          when the whole solution with it substituted checks valid; at most
          eight such rows per refinement.  Each row is recorded as a
          refinement of its own, so under [joint_term_alternatives] the check
          offers it as one tuple and itself picks among the rows, instead of
          the model deciding which boundary value (a task flag at 1) the
          initial state takes.  Rows are terms added to term sets, so offers
          only grow and a win is a win of the stated strategy; no answer rule
          is added.  Off, one row per refinement as before. *)
  name_large_check_disjunctions : bool; [@default true]
      (** Before a strategy check is converted to clausal form, every formula
          whose clause count (read off its structure) exceeds 1000 has its
          multiplying disjunctions named: bottom up, at a disjunction whose
          operands' clause counts multiply to more than their sum plus one,
          each operand with more than one clause and only negative predicate
          atoms becomes a fresh ordinary predicate applied to the universals
          it mentions, defined by one Horn clause.  The clausal form
          distributes a disjunction over conjunctions, so a chain of guarded
          cases each offering a choice of moves has a number of clauses
          exponential in its length: an elevator game's check with five
          floors did not finish its conversion within 3 GB.  Exact: the named
          system is satisfiable iff the original is, and unfolding the names
          in a refutation gives a refutation of the original, so the checks
          decide what they decided and the plays read off them are the same
          plays; an answer still comes only from a won check.  Off, every
          formula is converted as it is. *)
  name_check_disjunctions_by_size : bool; [@default true]
      (** Read with [name_large_check_disjunctions].  A formula within its
          1000-clause bound has its multiplying disjunctions named too when
          the named form's clausal size is smaller: the clause count times
          the formula's size as a tree, summed over the named formula and its
          definitions, against the same product for the formula.  The
          guarded clausal form repeats the predicate-free part of every
          conjunction a distribution goes through in each clause it builds,
          so a disjunction of a few moves, each conjoining a ranking
          substituted at its successor, became a few dozen clauses each
          carrying every move's ranking: one game's check grew from 28,110
          nodes to 25,510,650 in its conversion while its clause count stayed
          at 525, and the check's own preprocessing outlasted its budget
          before the solver was asked.  Exact, by the argument of
          [name_large_check_disjunctions]; only which formulas are named
          changes.  On by default: the smaller clausal form also changes
          Spacer's search, and a game whose largest check fell from 63 clauses
          of 31,567 nodes to 24 of 5,063 was answered in two or three runs of
          three instead of none or one.  Off, a formula within the bound is
          converted as it is. *)
  reuse_check_on_retry : bool; [@default true]
      (** When a side's check is asked again for the same strategies of both
          sides (after a timeout, at a doubled budget), reuse the check built
          for the previous ask instead of building it again.  The build reads
          only the strategies, the checked side's problem and the
          configuration, so a rebuild differs only in the fresh names it draws
          for named alternatives and disjunctions (and in which equivalent
          terms a solver-backed deduplication with its own small timeout
          happened to merge); the reused check is one this code built for
          those very strategies.  On a check with ten thousand placed term
          alternatives each rebuild took 17-25 s.  Off, every ask builds its
          check anew. *)
  skolem_term_window : int option; [@default None]
      (** [Some n] ([n >= 1]): a Skolem key keeps at most its [n] most recent
          terms.  When a refinement adds a term to a key that already has [n],
          the term added longest ago (the initial term counts as the oldest)
          is dropped; a term proposed again counts as new.  The keys refined
          by one counter-play are typically the choices of one transition,
          and the check offers every combination of their terms, so on a
          733-key game the opponent's check grew from 442 to 10,198 clauses in
          four turns although each key held at most five terms.  Term sets
          only offer strategies, and an answer still comes only from a won
          check, so no verdict changes; but a term set no longer only grows,
          so the loop's progress argument (each accepted refinement changes a
          term set within a finite set) does not apply, and a strategy can
          recur.  [None]: term sets only grow, as before. *)
  joint_term_alternatives : bool; [@default true]
      (** Read only when [miniscope_term_alternatives] and
          [name_term_alternatives] are on, for the ordinary check and the
          check with freed values (the copy-blind encoding keeps the
          product).  Skolem keys that every
          refinement so far has refined together (the nondeterministic
          choices of one transition, typically) are offered in a clause as
          ONE choice per refinement -- the tuple of terms that refinement
          proposed for them -- plus the combinations of the terms they held
          before their first refinement, instead of every combination of
          their terms.  The keys of a clause then contribute a number of
          alternatives bounded by the number of refinements rather than a
          power of it: on a 733-key game seven keys refined together made
          [2^7] alternatives after one refinement although only two tuples
          had been asked for.  Term sets still only grow and the offered
          tuples only grow, so the progress argument is kept; a won check is
          a won check of the product as well, since each clause offers a
          subset of the product's alternatives, so no answer rule changes.
          Combinations of terms from different refinements are no longer
          offered until a refinement proposes them, so a check the product
          would win can be lost.  Keys related by nesting are grouped so that
          the clause is still offered exactly the projection of the classes'
          rows. *)
  joint_term_alternatives_min_keys : int; [@default 4]
      (** Read only with [joint_term_alternatives]: a class of keys refined
          together is offered as rows only when at least this many of its keys
          occur in the clause; a smaller part is offered the product of its
          keys' term sets.  A part only shrinks as classes split, and a new
          class's rows contain every combination offered before it was
          formed, so a clause's offer still only grows.  The default is 4:
          with 2, a two-key class lost a winning strategy that combines two
          refinements' terms, while 4 keeps it and still bounds the large
          classes whose products made the checks grow. *)
  joint_rows_distinct_terms : bool; [@default true]
      (** Read with [joint_term_alternatives]: each member's term list is
          reduced to its distinct terms (first occurrences kept, in order)
          before a class's rows are formed as products.  One read-back records
          a key's terms once per copy of the key in the counter-play, so a
          list can repeat one term dozens of times, and the product over a
          class of four keys then lists every combination of the repeats
          before the repeated rows are dropped (1,679,616 rows reduced to 11
          on one check).  Exact: the rows after the existing deduplication are
          the same list, in the same order -- a row first occurs, in the
          product of the lists in lexicographic order, at the first
          occurrences of its terms, and those positions are ordered as the
          positions in the reduced lists. *)
  extra_plays_at_initial_budget : bool; [@default false]
      (** Read only when [counter_plays_per_check] is above 1.  Ask each extra
          counter-play at [chc_initial_timeout] (or the check's own budget when
          that is smaller) instead of at the budget of the check that returned
          the first play.  The check budget only grows (it doubles after every
          timeout and is never reset), so once one check has needed a large
          budget every later extra query may take that long too: two extra
          queries at a 32 s budget took 29 s and 42 s on a game whose checks
          at that point returned in 0.3 to 7 s.  An extra play only adds chain
          pairs and its absence never fails a refinement, so a shorter budget
          changes which pairs are asked, and with them the trajectory, but
          adds no rule by which an answer is given. *)
  extra_plays_inherit_lemmas : bool; [@default false]
      (** Read only when [counter_plays_per_check] is above 1.  Seed each
          extra counter-play query with the lemmas Spacer learned in the solve
          that returned the previous play (the check's, or the previous extra
          query's), when that was a Spacer solve in this process.  The extra
          query is that system with more body atoms guarded, so it derives
          nothing the earlier one does not, and each lemma, an
          over-approximation of what is derivable within its level, stays
          one for it: the query asked is the same, and only what Spacer has to
          re-learn is saved.  Without it each extra query is a fresh solve
          that shares nothing with the one before.  The solver may return a
          different play than the unseeded search would, so the trajectory
          can change; an extra play never decides an answer. *)
  extra_plays_budget_factor : float option; [@default None]
      (** Read only when [counter_plays_per_check] is above 1.  [Some c]: ask
          each extra counter-play at [c] times the seconds the check that
          returned the first play took (at least 1 s, at most the check's own
          budget), instead of at that budget, which only grows: it doubles
          after every timeout of either side and is never reset, so once one
          check has needed a large budget every later extra query may run that
          long, whatever the check at hand cost.  An extra query is the same
          check with earlier plays' exits blocked, so a play it can return is
          found in about the time the check took (on [warehouse-clean] and
          [warehouse-stock] the plays found took 2-6 s after checks of 3-7 s);
          one that runs much longer is usually asking whether no other play
          exists, the direction of a win, and ends at its budget.  An extra
          play only adds chain pairs and its absence never fails a
          refinement, so the factor changes which pairs are asked, and with
          them the trajectory, but adds no rule by which an answer is given.
          Takes precedence over [extra_plays_at_initial_budget].  [None]: as
          before the field existed. *)
  detect_unchanged_refinement : bool option; [@default None]
      (** Treat a refinement whose strategy is unchanged -- compared on the
          simplified first-order form, so that joining a ranking already present
          counts as no change -- as a failed refinement, which passes the
          turn (two in a row answer [unknown]).  [None] follows
          [name_opponent_decisions]. *)
  unchanged_reads_joint_offer : bool; [@default true]
      (** Read only where the joint offer is in use ([joint_term_alternatives]
          with [miniscope_term_alternatives] and [name_term_alternatives]).
          [true]: a refinement is rejected as unchanged -- by
          [detect_unchanged_refinement] in the turn loop and by the demonic
          fallback -- only when its term sets are unchanged *and* it proposed
          no tuple outside the joint offer of the check before it.  Under the
          joint offer a class of keys is offered its rows, not the product of
          its term sets, so a new combination of terms each key already held
          is one more alternative for the opponent's next check; comparing
          term sets alone called it a stall and, with a stall of the other
          side, answered [unknown] on a game the next checks win.  [false]:
          term sets alone decide, as before the field existed.  Either value
          leaves every answer rule as it is: the field decides only whether a
          refinement is kept or the turn is passed. *)
  chc_timeout_policy : chc_timeout_policy; [@default Global_doubling]
      (** See [chc_timeout_policy].  Absent, the check is scheduled as it was
          before the field existed. *)
  pass_turn_on_strategy_timeout : bool; [@default false]
      (** Read only under [chc_timeout_policy = Global_doubling].  When the
          check of a side that has a strategy unknown (a ranking or a Skolem
          key) times out and nothing its timeout triggers decided it (the
          ground split, the copy-blind re-check, the demonic fallback), double
          the shared budget as [Global_doubling] does and pass the turn to the
          other side, as [Pass_turn_on_timeout] does; the timed-out side is
          checked again, at the doubled budget, when the turn comes back.  A
          side with no strategy unknown is retried on the same side as under
          [Global_doubling]: its check is the whole question, and passing it
          is what made [Pass_turn_on_timeout] lose games whose strategy-less
          side answers only at a large budget.  Under [Global_doubling] one
          side whose check the backend cannot decide holds the run, and the
          other side's strategy, which that check's counter-play would
          refine, is never checked against the latest strategy of the first.
          A timeout is never a verdict and the turn order is no answer rule,
          so this changes when and whether a run answers, not which rule an
          answer rests on. *)
  empty_strategy_chc_solver : PCSPSolver.Config.t ext_file option;
      [@default None]
      (** The solver for the strategy check when the checked side has no
          strategy unknown at all (both of its strategy maps empty).  Then
          nothing is substituted into the checked side, so its CHC is the whole
          question of whether that side wins, and its answer is read without a
          counterexample: satisfiable is [valid], unsatisfiable is [invalid]
          (the empty-strategy shortcut), whatever solver produced it.  So a
          solver other than [chc_solver] -- one that need not return a
          counterexample, such as PCSat -- decides the same CHC by the same
          rule.  It is called with the same budget, an [unknown] from it goes
          to [backup_chc_solver] and a timeout is scheduled by
          [chc_timeout_policy], exactly as for [chc_solver].  [None] uses
          [chc_solver], which is the behaviour before the field existed.  A
          checked side with a strategy always uses [chc_solver], since its
          refinement needs the counterexample. *)
  strategy_free_race_solver : PCSPSolver.Config.t ext_file option;
      [@default None]
      (** A second backend raced, for the whole run, on the check of a side
          with no strategy unknown at all (both of its strategy maps empty).
          That check is the side's whole question -- nothing is substituted
          into it, and it does not change from turn to turn -- and it is read
          without a counterexample (satisfiable is a win, unsatisfiable a
          loss), so any sound solver may decide it.  At the first ordinary
          check of such a side, a forked copy asks this solver, with no
          budget, the check's co-CHC form: every predicate [P] replaced by
          its complement [not P], which takes the CHC over complement
          predicates back to the side's own clauses with disjunctive heads
          (the form MuVal's constraint solving reads).  The two forms are
          satisfiable together: [S] solves the co-CHC form exactly when
          [P |-> not S(P)] solves the check.  A [Sat] of the copy is read as
          a win of the check with that complemented solution (so the
          test that discards a win refuted by its own solution reads it), an
          [Unsat] as the check's refutation with no counterexample, which is
          how a side without strategy unknowns is refuted in any case;
          anything else ends the copy silently.  The copy takes the run over
          from its answer, as a continued copy does, and is stopped when the
          run answers.  The process meanwhile goes on as without the field,
          the other side's turns included.  Why: on games where the side that
          makes no decision of its own must close an invariant (a nu-only
          safety game whose choices are disjunctions, which are not strategy
          unknowns), Spacer runs out of every rung of the check while
          template-based solving finds the invariant.  [None]: no race. *)
  name_term_alternatives : bool; [@default true]
      (** How the check of a term-set strategy is encoded.  Off, a clause
          mentioning Skolem keys with term sets [T_1 .. T_m] becomes the
          disjunction of its [prod |T_i|] instances, and the CNF conversion of
          that disjunction is the product of the instances' clause counts --
          exponential in the number of alternatives.  On, two exact changes:
          (a) each key's term set is first deduplicated semantically (two terms
          equivalent under every value of the key's parameters are one
          alternative; a disjunction is idempotent), and (b) where the product
          of the alternatives' clause counts exceeds their sum plus one and the
          clause has one common head (or none) and no positive atom in any
          alternative's remainder, alternative [tau] is named by a fresh
          ordinary predicate [N_tau] over the universals the remainder [R_tau]
          mentions, defined by [N_tau(z) \/ R_tau], and the clause becomes
          [H \/ not N_1 \/ .. \/ not N_k] -- a Tseitin-style definitional
          encoding that leaves the check's satisfiability unchanged and makes a
          derivation the old one with [N] nodes interposed.  A clause of any
          other shape keeps the disjunctive encoding. *)
  miniscope_term_alternatives : bool; [@default true]
      (** Read only when [name_term_alternatives] is on.  Where in a clause a
          key's term alternatives are made.  Off, each key's terms are
          substituted into the whole clause, so a clause mentioning keys with
          term sets [T_1 .. T_m] has [prod |T_i|] alternatives even when the
          keys occur in unrelated parts of it -- two existential blocks in two
          disjuncts of one fixpoint body give [|T_1| |T_2| |T_3| |T_4|]
          alternatives where [|T_1| |T_2| + |T_3| |T_4|] suffice.  On, each
          key's alternatives are made at the smallest subformula of the
          clause's negation normal form, under conjunctions and disjunctions
          only, that holds every occurrence of the key and of its result
          variable, the operands of one connective being grouped by the keys
          they share; and each set of alternatives, wherever it sits, is
          named by fresh predicates under the conditions [name_term_alternatives]
          uses at the top of a clause.  Exact: a context built from [and] and
          [or] alone distributes over a disjunction in its hole, and naming an
          alternative at a position under [and]/[or] only is exact for the same
          monotonicity reason as at the top, so the check decides the same
          question as with the field off and only its size changes.  The
          strategy check decides every answer either way.  Off, the
          whole-clause substitution, as before the field existed. *)
  select_prefer_bound : bool; [@default true]
      (** Read only when [refine_terms] is [Terms_select].  The published
          model-guided selection over the reals takes the midpoint of the
          tightest lower and upper bounds that hold at the model, so a key
          whose result the formula confines to a constant interval
          [\[-c, c\]] always gets the constant [0], the least extreme move.
          On, each key whose result is bounded on both sides first gets the
          end of its admissible interval nearer the model's value (the bound
          itself when the formula holds there, a point just inside it
          otherwise); the whole solution is checked valid, then the same with
          the farther ends, and the first that passes is used.  When neither
          passes, or no key is bounded on both sides, the selection is the one
          used with the field off.  Copies of one key may now get different
          ends, which [refine_guards = Separation] then combines.  The strategy check
          is unchanged, so this changes which strategy is proposed and never
          how an answer is decided. *)
  relative_completeness : relative_completeness_mode; [@default Rc_off]
      (** See [relative_completeness_mode].  Refused together with
          [skolem_term_window], which drops terms and so would undo an offer.
          Offers and probes only add alternatives and checks: an answer still
          comes only from a won check, and a won probe's rankings are
          ranking-function relations, well-founded and transitive by
          construction. *)
  offer_every : int; [@default 4]
      (** Read only with [relative_completeness] not [Rc_off]: an offer and a
          probe are made on every [offer_every]-th turn of a side (at least
          1).  Any value keeps the guarantee, which needs only infinitely many
          of them; a larger one grows the checks more slowly.  4 because, of
          1 and 4 on the 47 POPL 2024 games at 60 s, 1 answered fewer: each
          offer adds one alternative per Skolem key to every later check of
          its side, and the losses were files whose checks the default
          decides near the budget. *)
  select_snap_constant_keys : bool; [@default false]
      (** Read only when [refine_terms] is [Terms_select], and only over the reals.
          A Skolem key of the refuted side that takes no argument (an initial
          choice, such as a game's starting position) gets a constant term,
          and the selection read it off the solver's model or an end of its
          interval: a value from a continuum, so a key refined again and again
          collected a new constant each time and its term set never stopped
          growing, and the strategy checks with it.  On, before the selection
          pass the result of each such key is moved, within the values at
          which the weakened formula still holds with the other variables
          fixed, to the existing constant of that key nearest the model's
          value, or when none is admissible to the simplest rational (least
          denominator, then least absolute value) of the eighth of the
          admissible interval at the end nearer the model's value -- an
          opponent's winning initial choice is often an extreme one -- and the
          selection then keeps it.  A key whose result is a linear term has one
          of its variables moved so that the term's value is chosen this way.  Term sets still only grow and the
          solution is checked valid as before, so this changes which strategy
          is proposed and never how an answer is decided.  Off, the selection
          is the one used before the field existed. *)
  counter_plays_per_check : int; [@default 1]
      (** How many counter-plays one failed strategy check hands to the
          opponent's ranking refinement.  At 1 (or any value below it) the refinement learns from the single derivation the CHC
          solver returns, as before the field existed.  1 by default (it was
          3): measured with [wp_share_choice] and
          [resynthesise_only_on_new_pairs] on, on 1,424 termination and muCLP
          inputs at 300 s, the three together answered 7 inputs the previous
          defaults did not and lost none, with no two runs giving opposite
          verdicts and 0.89 of the time in sum on the inputs both answered
          (median ratio 0.94).  The extra queries each take up to a check's
          budget, and on one muCLP input that only the new defaults answered
          the previous ones had recorded over a hundred extra counter-plays
          without an answer.  At [k > 1], and only
          under [chain_pairs_from_play], the check is asked again up to
          [k - 1] times, each time with the exits of the plays found so far
          blocked as premises -- the side premises by which a play reaches the
          query or leaves a chain of a ranked predicate, never a ranked visit
          -- so that the solver has to return a different play, one that
          continues a chain further or uses another side premise; the chain
          pairs of every play found go to the one ranking copy per key.  Each extra query has the budget
          of the check that returned the first play, so a check takes at most
          [k] times its budget; a query that times out, answers anything but a
          counter-play, or fails ends the collection.  The blocked system is a
          weakening of the checked one, so each extra play is a real
          counter-play of the checked strategy, and a refinement that fails
          with the extra pairs is retried with the first play's pairs alone.
          The strategy check is unchanged, so this changes which strategies
          are proposed and never how an answer is decided. *)
  drop_tautological_check_clauses : bool; [@default false]
      (** Remove from the strategy check, before it goes to the CHC backend,
          every clause whose head holds an atom its body also holds (the same
          predicate on syntactically equal arguments).  Such a clause is valid,
          so the check keeps its solutions, and the remaining clauses are a
          subset, so each counter-play the backend returns is one of the
          original check: the answer and the refinement's input are those of
          the unreduced check, and only the backend's search changes.  Off,
          the check reaches the backend as before the field existed. *)
  copy_blind_choices : bool; [@default false]
      (** Whether a choice the checked side leaves open in the body of a
          predicate that carries a remembered copy may depend on the copy.  The
          disjunctively well-founded reduction gives a least-fixpoint predicate
          and the members of its component a copy of an earlier visited state,
          chosen by the refuting side, and the check is satisfiable exactly
          when the reduced greatest-fixpoint system holds at the query; so a
          disjunct, or a term of a key's term set, that is still open in such a
          body is resolved pointwise in the copy, which can make an invalid
          input's check satisfiable under a union of well-founded rankings.
          Off, such choices stay open, as before the field existed.  On, in
          every such body each choice node with two or more alternatives
          (disjuncts or term alternatives that mention a fixpoint predicate or
          the copy) is replaced by one fresh ordinary predicate per alternative
          whose arguments are the body's variables other than the copy (the
          predicate's original arguments, the enclosing binders and the flag);
          the alternative must then win at every copy value at which the
          position is reachable, where reachability is a further fresh
          predicate per fixpoint predicate, defined by Horn clauses that follow
          every call from the query.  The check stays a CHC, and a satisfiable
          check is one the checked side wins with choices that do not read the
          copy; it can lose answers the unrestricted check gives, never add
          one.  A check whose formulas this encoding cannot read is not taken
          as a win, and a failed refinement passes the turn rather than
          answering. *)
  check_refinement_kinds : bool; [@default false]
      (** A diagnostic, meant for debugging configurations only: when a
          refinement is accepted, re-check the kind constraints of the
          solution PCSat returned for it -- for each ranking copy, declared
          [DWF], that the solution lies inside the decrease relation of the
          ranking certificate the template recorded, which makes every piece
          well-founded -- and print a
          [(refinement-kind-check (passed N) (unchecked N) (failed N))] line.
          The check reads the answer and never changes it: a failed check is
          printed, and the refinement is used as it would be without it.  It
          costs one Z3 call per kinded unknown per refinement. *)
  copy_blind_on_timeout : bool; [@default true]
      (** When the ordinary strategy check of a side whose clauses carry a
          remembered copy times out, check the same strategies with
          [copy_blind_choices]'s encoding at the same budget before the budget
          is doubled.  A win there is an answer, as under
          [untransitive_win]'s re-check; a counter-play there refines the
          opponent, and a failed refinement from it passes the turn.  If that
          check yields neither, the timeout is handled as without the field.
          The copy-blind check makes every choice independent of the copy and
          is sometimes decided within the budget where the ordinary check is
          not.  On by default: it adds no answer rule, and on the POPL 2024
          games and nine smaller inputs it answered three files the default
          did not (one a game only the fixpoint-logic solver had answered) and
          lost none.  Off, a timeout is handled as before the field existed. *)
  copy_blind_recheck_once : bool; [@default false]
      (** Under [copy_blind_on_timeout]: ask the copy-blind re-check of one
          check (the same side, the same strategies of both sides, the same
          problem) at most once.  Once that re-check has given neither a win
          nor a counter-play, the retries of the same check at the doubled
          budgets skip it, and their timeouts are handled as without
          [copy_blind_on_timeout].  A check of other strategies is still
          re-checked once, at whatever budget it times out.  Without the
          field every rung of the doubling asks the ordinary check and then
          the copy-blind re-check, so a run that climbs the ladder pays each
          budget twice, and the last two rungs are most of its time.
          Skipping a re-check removes a question, never an answer rule, so it
          can lose or gain answers but not change a verdict.  Off by default:
          some checks are decided by the copy-blind re-check only at a higher
          budget (one goal-corpus input answered at about 100 s by the third
          re-check, at budget 32, every time, and never under the field),
          while the time it frees went to ordinary checks that still did not
          decide; on 1,471 inputs at 300 s the two settings answered within
          one input of each other. *)
  copy_blind_recheck_continued : bool; [@default false]
      (** Under [copy_blind_on_timeout]: ask the copy-blind re-check of a
          timed-out check in a forked copy with no budget, and do not wait
          for it.  The process handles the timeout at once as when the
          re-check gives nothing (the next steps, then the doubling); the
          copy goes on asking while the retries of the same check run, and a
          retry finding it still running asks no re-check of its own.  When
          the copy decides -- a win of an established encoding or a
          counter-play with its derivation, the answers the waited re-check
          reads -- it takes the run over from the point where it was
          started, as a continued ordinary check does.  The copy is stopped
          when a check of other strategies is asked.  So each rung's budget
          is paid once in wall time instead of twice, and the re-check is
          no longer cut at each rung and asked again from nothing.  Every
          answer read is one the waited re-check reads, from the same check
          and solver; only the time it is read changes, and a re-check that
          would have decided only after its rung's budget is now read too.
          Costs one more core while the copy runs.  Takes precedence over
          [copy_blind_recheck_once] for the checks it starts. *)
  copy_blind_first : bool; [@default false]
      (** Check a side's strategies with [copy_blind_choices]'s encoding
          first, at the check's budget, and ask the ordinary check only when
          that yields neither a win nor a counter-play (a timeout, or an
          encoding that is not established or exceeds
          [copy_blind_max_premises]).  A copy-blind win is an answer and a
          copy-blind counter-play refines the opponent, as under
          [copy_blind_on_timeout]; the ordinary check that follows does not
          repeat the copy-blind check on its own timeout.  The copy-blind
          encoding is a fifth to a ninth of the ordinary one's size, and with
          a winning ranking the ordinary check was the one that timed out.
          Off by default. *)
  copy_blind_max_premises : int; [@default 2_000_000]
      (** An upper bound on the copy-blind encoding's size, counted as the
          premise literals of the clauses it emits (each choice definition and
          each reachability clause carries the premises of its path), checked
          while the encoding is built.  Above it the encoding is abandoned and
          the check is not asked copy-blind: a re-check after a timeout is
          skipped (the timeout is handled as without [copy_blind_on_timeout]),
          and a win that was to be certified, or a check under
          [copy_blind_choices], is treated as not established.  The bound
          protects the process's memory: the premises are copied into every
          clause below a node, so their total can grow with the square of a
          formula's size, and a formula with five Skolem keys of six terms each
          placed at one subformula (7,776 alternatives) exhausted about 10 GB
          before the encoding kept each term alternative's own disjuncts apart.
          Abandoning the encoding can only lose an answer the copy-blind check
          might have given; it never makes one. *)
  reask_undecided_check_inline : bool; [@default false]
      (** When an ordinary strategy check times out, ask the same CHC once more,
          at the same budget, of [reask_inline_chc_solver], a verdict-only
          Spacer with Z3's rule inlining turned on, before anything else the
          timeout triggers ([copy_blind_on_timeout], the doubling).  Only a win
          (the query not derivable) is taken, and it is handled as a win of the
          ordinary check, so the copy-blind certification of a ranking not
          proved transitive still runs after it; a counter-play or anything
          else from the re-ask is discarded and the timeout is handled as
          without the field.  Z3's rule transformations keep whether the query
          is derivable; they are off in the ordinary check only because the
          derivation read back after them may not be one of the original
          rules, and a win reads nothing back.  On a check where the
          multiplying disjunctions are named by predicates
          ([name_large_check_disjunctions]), inlining them back inside Z3 cut
          one undecided check from 54.7 s to 11.7 s standalone.  Off by
          default. *)
  reask_inline_chc_solver : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/gspacer_inline_verdict.json"]
      (** The solver of [reask_undecided_check_inline]'s re-ask.  Only its
          [Sat] (a win) is read. *)
  reask_undecided_check_plain_spacer : bool; [@default false]
      (** When an ordinary strategy check (asked of [chc_solver], not a
          retry by [backup_chc_solver]) times out, ask the same CHC once
          more, at the budget it just timed out at, of [backup_chc_solver],
          after [reask_undecided_check_inline] and before anything else the
          timeout triggers ([copy_blind_on_timeout], the doubling).  A win
          or a counter-play with its derivation is read exactly as the
          ordinary check's (the counter-play goes to the refinement, the
          named re-ask of [chain_pair_regions_free_opponent_values]
          included); anything else is discarded and the timeout is handled
          as without the field.  The shipped [backup_chc_solver]
          ([config/solver/spacer_cex.json]) is the ordinary check's Spacer
          ([gspacer_cex_noconc.json] in the shipped configurations) with
          global guidance off, the same
          transformations off and the same counterexample read-back, so
          the answers are trusted for the same reason.  Which of the two
          settings decides a check first differs from check to check: one
          check undecided by the default at 120 s is a win in 10 s without
          global guidance.  Off by default. *)
  race_check_plain_spacer : bool; [@default false]
      (** Ask every ordinary strategy check (one that
          [reask_undecided_check_plain_spacer] would re-ask on a timeout)
          of [backup_chc_solver] as well, in a forked copy started beside
          the in-process check with the same budget, and let the first of
          the two that decides make the run.  When the copy decides first
          (a win, or a counter-play with its derivation) it takes the run
          over and continues it from that answer exactly as the process
          would have continued from the same answer of the ordinary check;
          the process stops and exits with the copy's status.  When the
          process decides first, the copy is killed.  When the in-process
          check times out, the process waits at most [race_timeout_grace_ms]
          (2 s) more for the copy, then kills it and handles the timeout as
          without the field (the sequential re-ask of
          [reask_undecided_check_plain_spacer] is then not asked: the copy
          has asked it).  No budget is spent in sequence; the cost is a
          second core and up to a second copy of the heap while a check
          runs.  No race is started when duplicating the major heap would
          not fit in the memory cgroups' headroom or the fork is refused
          (a domain running); the check is then asked as without the
          field.  Off by default. *)
  continued_check_flat_and_or : bool; [@default true]
      (** Read only with [continue_check_in_copy] (or [check_in_copy_only]).
          The forked copy that goes on asking an ordinary check hands it to
          the check's solver with every nest of conjunctions and disjunctions
          written as one n-ary application ([Z3interface.with_flat_and_or]),
          while the process asks it as written.  Both are the same check, so
          either answer (a win, or a counter-play with its derivation) is the
          check's; only which search is run beside the process's changes.
          Why: Spacer's search on a strategy check depends on the shape it is
          handed, and on the games where it is slow the two shapes are slow
          on different checks -- on a cinderella game the flat form was
          decided in 9 s by the copy where the written form was not within
          60 s, and on another the written form was decided in 2 s where the
          flat one was not within 60 s.  The process asks the written form at
          the first budget as before, so a check decided there is decided as
          without the field; at each later rung, where it would only wait for
          the copy, it asks the written form again from nothing at that
          rung's budget, so that neither shape's search is given up while the
          other runs (a check the written form decides only past the first
          budget is still decided by it). *)
  continue_check_in_copy : bool; [@default true]
      (** Keep the work of an ordinary strategy check that runs out of its
          budget instead of restarting it.  Each check makes a solver context
          of its own and drops it on return, so without the field a check
          undecided at budget [b] is asked again from nothing at [2b] after
          the timeout's other questions (the copy-blind check among them):
          a check needing [T] seconds with [b < T <= 2b] costs [b], then
          those questions, then [T] more.  With the field, a forked copy of
          the process asks the same check of the same solver with no budget
          beside the in-process check.  The process keeps an answer it finds
          within [b] (the copy is killed; a copy that decided first waits
          until [b] has passed since it started before claiming, so the
          process's own answer to the same question is not taken from it);
          when the process's check times out, the copy goes on while the
          process handles the timeout as before, and at the retry of the
          same check at each doubled budget [B] the process asks nothing:
          it waits until the copy has run [B] seconds and, if the copy has
          not decided by then, handles that rung's timeout in turn.  A copy
          that decides (a win, or a counter-play with its derivation) takes
          the run over from that answer, with the check's budget raised to
          the rung at which the doubling schedule would have decided it.
          The copy is killed as soon as the process asks any other check or
          answers.  Every answer is an answer of the same check by the same
          solver, so no answer rule is added.  Not used together with
          [race_check_plain_spacer] or
          [race_check_plain_spacer_after_first_rung] (that race is asked
          instead).  No copy is started when duplicating the major heap would not fit
          in the memory cgroups' headroom or the fork is refused.  On by
          default: on checks decided within the first budget the duplicate
          ask costs about a fifth more time and a third more memory, and a
          copy that answers alone (no duplicate ask) costs more, because a
          counter-play cannot be carried back to the process and every
          decided check then hands the run over. *)
  check_in_copy_only : bool; [@default false]
      (** The schedule of [continue_check_in_copy] with each ordinary check
          asked once instead of twice: only the forked copy asks it (of the
          same solver, with no budget), and the process asks nothing during
          the check's first budget [b]; it waits for the copy, outside any
          solver call.  A copy that decides takes the run over from its
          answer at once (the process then exits with the copy's status, as
          any process whose race a copy won); when the copy has not decided
          once [b] has passed, the process handles the check's timeout
          exactly as under [continue_check_in_copy] (the ground split, the
          copy-blind re-check in a second copy, the waits at each doubled
          budget), so the run asks the same questions and reads the same
          kinds of answers.  A copy that ends within [b] without an answer,
          and a check for which no copy can be started (the major heap would
          not fit in the cgroups' headroom, or the fork is refused), are
          asked in the process as without either field.  Every decided check
          is a hand-over, so the run passes from copy to copy; each process
          handed over waits for its copy until the run ends.  Not used
          together with [race_check_plain_spacer] or
          [race_check_plain_spacer_after_first_rung].  Off by default. *)
  race_check_plain_spacer_after_first_rung : bool; [@default false]
      (** The race of [race_check_plain_spacer], started only for an
          ordinary check whose budget is above [chc_initial_timeout] -- a
          check asked at a later rung because a check of the same side (of
          both sides under [Global_doubling]) already ran out of a budget.
          A check asked at the first budget is asked of the main solver
          alone, as without either field, so a run whose checks all decide
          at their first budget forks nothing.  Racing a check costs a
          second core and up to a second copy of the heap for the whole
          check; most checks are decided within the first budget, where a
          copy gains at most the difference between two times both under
          that budget, while the plain setting has decided a check that
          global guidance left open only at a later rung.  Implied by
          [race_check_plain_spacer] (which races every rung).  Off by
          default. *)
  split_ground_alternative_goals : bool; [@default true]
      (** When an ordinary strategy check times out and its goals are
          conjunctions of ground atoms -- the check names each of the checked
          side's term alternatives by a nullary predicate defined by clauses
          without variables, such as [U(1, 1) => Alt_1], and a goal needs all
          of them -- decide each ground atom's derivability on its own by a
          ground top-down search, before anything else the timeout triggers.
          When some goal has every atom derived, the counter-play is that
          goal's clause over the separate derivations, every clause instance
          re-checked by evaluation, and it is handled as the ordinary check's
          counter-play (the extra counter-plays of [counter_plays_per_check]
          are asked of the same search).  A failed search proves nothing and
          the timeout is handled as without the field; no win is ever read
          from it.  The conjunction is what makes such a check nonlinear: one
          check of four alternatives of about 100 steps each was undecided by
          Spacer at every budget while each alternative alone is derived in
          under a second.  On by default. *)
  split_ground_prove_leaves : bool; [@default false]
      (** Read by [split_ground_alternative_goals].  When the split derives no
          goal, show leaves not derivable instead: each leaf the search did not
          derive is asked of the check's own solver as the only goal of the
          check's other clauses, in rounds of 1, 2, 4, .. seconds per leaf,
          all of them within the budget the check just ran out of.  As soon as
          the leaves shown not derivable, with every other leaf derivable,
          leave every goal underivable, the check is a win, handled as the
          ordinary check's win (its certification included).  The conjunction
          of named alternatives is what makes such a check hard for Spacer: a
          warehouse game's check whose initial-state rows include one the
          opponent cannot answer was undecided at 8 s, while that row alone
          was decided in 5-14 s.  A proof not found says nothing, and the
          timeout is then handled as without the field. *)
  split_ground_alternative_budget : int; [@default 200000]
      (** The number of clause instances [split_ground_alternative_goals]'s
          search may try per ground atom. *)
  split_ground_alternative_max_asks : int option; [@default Some 0]
      (** Read by [split_ground_alternative_goals].  With [Some n], one split
          of a check asks Z3 for at most [n] clause instances in all (an
          instance whose head does not bind every variable of its clause);
          past that, such an instance is not found and the search goes on by
          matching alone.  [None]: no bound beyond the attempt budget.  Only
          which derivations are found changes, and a split that finds none
          is handled as the timeout it replaces, so no answer rests on the
          bound.  Why: the search is depth first in clause order and keeps no
          measure of progress, so on a grid walk it follows one direction
          until the attempt budget is spent, asking Z3 (up to 1 s) at every
          step; two such undecided splits cost 7 and 16 s of a 60 s run,
          while the check it was built for is split by matching alone (no
          question at all). *)
  split_ground_alternative_stop_when_doomed : bool; [@default true]
      (** Read by [split_ground_alternative_goals].  Stop the split as soon as
          the ground atoms not derived so far leave no goal derivable even if
          every atom not yet tried were derived (the propositional least
          model over the named alternatives, failed atoms false and the rest
          true).  The outcome is the same -- a split stopped this way finds
          no counter-play, as the full split would not either -- and only the
          time and the census counts change.  Why: each underivable atom
          costs the whole attempt budget, and on a check with 523
          alternatives of two atoms each, none derived, the split ran past a
          60 s run although the first alternative's two failures already
          made every goal underivable.  On by default (exact). *)
  split_ground_clause_heads : bool; [@default true]
      (** Read by [split_ground_alternative_goals].  State each clause of the
          composed counter-play with its own head, as Spacer states the
          clauses of a derivation, instead of with the node's ground
          conclusion in place of the head.  With the conclusion as the head,
          the stated clause [body /\ constraint => P(c)] no longer ties the
          body's variables to the ground head [c], so a chain-pair region
          read from it fixes the upper visit's state at the play's point and
          leaves the lower one bounded only by the guard on the body's
          variables: on a loop [x >= 0, y > 50: (x, y) -> (x - 1, y + 1)]
          the region was [(x, y) = (0, 52)] to [x' >= -1, y' >= 52], with no
          linear ranking, where the clause's own head gives [x' = x - 1,
          y' = y + 1, x >= 0, y >= 51], ranked by [x].  The derivation is
          the same either way (each node's conclusion is still read from the
          node); only the clause the refinement reads changes. Enabled by
          default with the ground-goal split package. *)
  split_ground_budget_after_cut : int option; [@default Some 5000]
      (** Read by a split that is given no budget of its own (not an extra
          play's under [split_ground_extra_play_budget]).  [Some n]: the
          split is asked with at most [n] clause instances per ground atom
          first, and again with [split_ground_alternative_budget] only when
          that left it undecided with some smallest-derivation exploration
          cut by the small budget, and no exploration at the configured budget
          has been cut earlier in the run; once one has, the later leaves of
          that split and every later split of the run are searched with [n]
          alone.  [None]: every split at the
          configured budget.  Before that first cut at the configured budget
          the outcome kind is the configured budget's (a leaf derived or
          proved underivable within fewer tries is so within more, and an
          undecided split with no cut explored all it could); after it, a
          split may give up where the configured budget would have derived a
          leaf or proved a win.  Sound for any value: the budget only decides
          when a search gives up, a derivation found is a derivation of the
          check's clauses and a win is read only from an exploration that was
          not cut.  Why: the configured budget (200,000 on the elevator
          games) buys the win proofs of games whose positions are finite,
          where every exploration empties its queue; on a game whose positions
          are unbounded no exploration does, so a leaf that is not derived
          spends the whole budget -- four such leaves of one robot check spent
          62 s, ending a run whose default answers in 1 s -- and the small
          first pass costs the finite games about [n] tries per leaf more.
          A cut at the configured budget is the observation that tells the two
          kinds of game apart. *)
  split_ground_large_pass_literal_box : bool; [@default false]
      (** Read with [split_ground_budget_after_cut]: the second pass of a
          split, at [split_ground_alternative_budget], is not asked when some
          leaf's exploration in the first pass reached an atom with an
          integer argument outside [-m, m], [m] the largest absolute integer
          literal of the check's clauses (at least 1); and when it is asked,
          its exploration of a leaf stops at the first such atom, as at a
          spent budget.  Sound for every input: only when a search gives up
          changes, a derivation found is a derivation of the check's clauses
          and a win is read only from an exploration that was not cut, and a
          split that gives up is handled as without the split.  Exact on every
          check whose explored atoms stay within that box -- in particular a
          game whose every position is bounded by guards against its own
          literals -- where no atom escapes and the passes are the ones
          without the field.  Why: the second pass buys the win proofs of
          finite games (the elevators, whose floors the guards bound), but on
          a game whose positions are unbounded its exploration never empties
          its queue; on a factorial loop the values grow along the play, and
          one second pass ran for 77 s at about 30 MB/s to 2.5 GB, where the
          run without it answers in 17 s.  An atom outside the literal box is
          the observation that the game explored is not one its guards bound
          by its literals. *)
  split_ground_extra_play_budget : int option; [@default Some 5000]
      (** Read by the extra counter-plays of a check whose counter-play the
          ground split composed ([counter_plays_per_check]): [Some n], each of
          their splits tries at most [n] clause instances per ground atom in
          place of [split_ground_alternative_budget]; [None], that budget.
          An extra play's split reads only a derivation, never a win, so the
          budget there only bounds how long a leaf that is not derived is
          searched.  Sound for any value: a derivation found is a derivation
          of the check's own clauses, and none found is an extra play not
          added, as when the search fails.  Why: an extra play blocks the
          exits of the plays before it, so its leaves are often not
          derivable at all, and on a game whose positions are unbounded the
          exploration of such a leaf never empties its queue: with the
          budget raised to 200,000 for the win proofs of the elevator games,
          each extra-play split of a warehouse game spent about 7 s and a
          60 s run spent 49 s in them. *)
  freed_reask_after_split_max_height : int option; [@default Some 1000]
      (** Read only with [split_first_freed_reask]: [Some h], the tagged
          re-ask is not asked after a counter-play the ground split derived
          before the solver whose derivation is higher than [h] nodes (the
          most nodes on a path from the query to a leaf); the split's
          counter-play is then read, as when the re-ask returns none, and the
          side's count of failed re-asks is left as it was.  [None], the
          re-ask is asked whatever the height.  Exact in verdict: the re-ask
          decides nothing, so only which counter-play the refinement reads
          can change.  Why: the tagged check has the same derivations as the
          check (each tag is defined to be exactly the strategy value it
          names), and the split's search returns a derivation of least size
          among those it explored, so a solver that unrolls the clauses level
          by level has to reach about that height to return any counter-play
          of the tagged check.  Where the split evaluated a deterministic loop
          concretely, a terminating loop run 1,500 times gave a derivation of
          7,509 nodes in a chain, and the re-ask spent its whole initial
          budget (8 s of an 18 s run) and returned nothing; the re-asks that
          return a counter-play after a split-derived one followed
          derivations of at most 57 distinct nodes on the input whose answer
          needs them.  The default [Some 1000] was measured with the
          nearest-visit chain pairs on: on 32 integer transition systems
          (the inputs where a split-derived play exceeds 1000 nodes, those
          near the bound, and random controls), four runs each, no answer
          was gained or lost, and on the two inputs whose time it moved the
          median run went from 13.3 s to 5.4 s and from 13.3 s to 5.1 s. *)
  split_first_freed_reask : bool; [@default true]
      (** Read only with [split_ground_goals_first]: a counter-play the
          ground split derives before the solver is followed by the tagged
          re-ask of [chain_pair_regions_free_opponent_values] (with its own
          budget and skip rules), exactly as a counter-play the solver
          returns is; when that re-ask returns a counter-play, it is the one
          the refinement reads.  Exact in verdict: the check is lost either
          way, and a counter-play of the tagged check is one of the check.
          Why: without it, every check the split decides skips the re-ask, so
          the regions read from it pin the checked side's values; on
          `function_tacas2013d`, which the default answers through those
          freed regions in 7-20 s, the split-first package refined for 57 s
          of 60 and answered in none of 6 runs. *)
  split_ground_goals_first_integer_only : bool; [@default true]
      (** Read only with [split_ground_goals_first]: that field applies only
          to an input whose predicates' parameters, and the variables its
          predicate bodies and query bind or leave free, are all of sort
          [Int] or [Bool] ([SplitFirstGate.applies]); on any other input the
          run is the one without [split_ground_goals_first].  Read off the
          input once, before any play; either way every answer is one the
          run with or without the field can give.  Why: on the real-valued
          warehouse and robot games the split derives a counter-play to most
          checks at once, and the smallest one fixes one real point per
          decision of a continuous opponent, so the refinement from it adds a
          point a turn -- on `warehouse-empty` the derived plays grew from 56
          to 4,032 nodes over seven turns and the run did not end within
          60 s, where the plays Spacer returns end it in about 2 s; the games
          the split decides (the elevators, whose wins it proves from a
          complete exploration, and a grid game) are over integers. *)
  split_ground_smallest_stop_at_root : bool; [@default true]
      (** Read only with [split_ground_goals_first].  The smallest-derivation
          search of a leaf stops exploring as soon as the leaf is derivable
          from the instances explored so far (and does not explore at all when
          an earlier leaf's derivation already holds it), instead of
          exploring until its queue is empty or its attempt budget
          [split_ground_alternative_budget] is spent; the derivation returned
          is then the least over the instances explored until that point.
          Exact in outcome: derivability over the explored instances only
          grows with the exploration, so whether a leaf is derived, proved
          underivable or neither is the same as without the field, and so are
          the split's outcome kinds (a win needs a complete exploration with
          no leaf derived, which is not cut short); only which counter-play
          is returned, and the tries spent, change.  Why: on a game whose
          positions are unbounded (a robot on a grid, a warehouse) the
          breadth-first exploration never empties its queue, so every leaf
          cost the whole budget of 200,000 tries although its derivation was
          among the first instances explored, and a 60 s run spent 45-52 s
          in splits asked before the solver. *)
  split_ground_goals_first : bool; [@default true]
      (** Read only with [split_ground_alternative_goals].  Ask the ground
          split of an ordinary check whose goals are over ground atoms BEFORE
          the check's solver, rather than only after the solver's timeout;
          when it derives a counter-play, the solver is not asked and that
          counter-play is the check's (its extra counter-plays asked of the
          same search, as after a timeout).  When it derives none, the check
          is asked as without the field, and its timeout does not run the
          split of the same check a second time.  A split that derives the
          counter-play of a check whose timed-out ask a forked copy still
          continues ([continue_check_in_copy]) also stops that copy.  And the
          split derives each ground atom by the smallest derivation over the
          clause instances it explores ([GroundGoals.derive_smallest]),
          rather than by the first one a depth-first search meets; when that
          exploration is complete (every clause variable fixed by the head,
          every constraint evaluated to true or false, the attempt budget
          [split_ground_alternative_budget] not exhausted) and leaves no goal
          derivable, the check is read as won.
          Sound: a derived counter-play is a derivation of the check's own
          clauses, every instance re-checked by evaluation, so it is a
          counter-play of the check whoever produced it; a win is read only
          from a complete exploration, which every derivation of a leaf would
          have to pass through, and goes through the arms of a solver's win
          (the copy-blind certification of a ranking not proved transitive
          included); a copy stopped after a counter-play could only have
          returned another counter-play, since the check has one.  Which
          answer is read, and when, changes.  The budget matters: the
          exploration's cost is linear in its tries (a few seconds for
          200,000), and on a five-floor elevator the default 5,000 tries ran
          out after 2,126 atoms, short of the whole game, where 200,000 tries
          proved the win of the ten-floor one in under a minute.  Why: on the elevator
          games Spacer leaves a check undecided at its 8 s budget whose
          counter-play the split then derives in 0.06-0.3 s; meanwhile a copy
          kept asking the check, decided it 15-35 s later and took the run
          over from the process, which had already refined from the split's
          play, and asked its two extra counter-plays of Spacer at the raised
          budget (37 and 80 s in two runs).  The smallest derivation matters
          because a check's step clause can conjoin one name per move of the
          branching player, so a derivation is a tree over every move, and
          the first one the depth-first search met had twenty million nodes
          on one check, where a move its constraint settles needs none. *)
  copy_blind_lift_kept : bool; [@default false]
      (** Read by [copy_blind_choices]'s encoding.  Give each node of term
          alternatives one more kept disjunct: the disjunction, over the
          node's alternatives, of the alternative's own kept disjuncts other
          than its result guards, with each result variable that has a guard
          [r <> t] in that alternative replaced by [t].  At every value of the
          results it implies the node (where a result differs from its term,
          that guard holds; where all agree, the kept disjuncts themselves
          do), so the formula's meaning is unchanged; if it mentions the copy
          or a predicate it is not added.  Its negation is a premise
          of every choice definition and reachability clause below the node,
          so a call inside one alternative is not followed when another
          alternative's kept disjunct already decides the node, as it was not
          when all alternatives' disjuncts formed one node.  Without it an
          alternative whose own result guard makes its kept disjuncts valid
          wins the node, yet the calls of the other alternatives are still
          reached, which can make a check unsatisfiable that the one-node
          grouping satisfied.  It adds premises and never removes one, so it
          can only make the check easier to satisfy on the reachability side,
          and the argument that a satisfiable established check is a win
          holds with it unchanged.  Off, as before the field existed. *)
  untransitive_win : untransitive_win; [@default Recheck_copy_blind]
      (** What a won check needs to be an answer when a ranking it substitutes
          is not proved transitive; see [untransitive_win].  A win whose
          rankings are proved transitive is an answer at once, so the
          copy-blind re-check of the default costs one extra check only when a
          ranking is not proved transitive.  On the POPL 2024 games and nine
          smaller inputs the re-check lost one answer the unguarded check
          gave, and the unguarded check answered an invalid query [valid]. *)
  chc_initial_timeout : int; [@default 8]
      (** The budget, in seconds, every strategy check starts from (both
          sides, main and backup solver).  A check that times out doubles it
          as [chc_timeout_policy] says, so a file whose checks are all slow
          spends about as long in the retries below the budget that answers as
          in that answer; a larger start saves those retries and costs time on
          a file whose checks are fast.  A budget decides only which check
          runs next and when, never a verdict.  On the POPL 2024 game corpus
          at a 60 s budget, starting from 8 answered every file that starting
          from 1 or 4 answered and two more often (a grid-reachability game 5
          of 5 runs against 0 of 5 from 1), so 8 is the default; 1 is the value
          this field replaced and is kept as a named configuration. *)
  init_fn_terms_product_bound : int option; [@default Some 1]
      (** A bound on the size of a side's initial Skolem strategy.  Each
          [FN] key starts from a SET of candidate terms: the default term of
          its result sort and every argument of that sort.  A clause mentioning
          several keys is checked against the product of their sets, so five
          keys over six real arguments start the first check at 7^5 = 16807
          alternatives, and building that check alone took 87 s on a five-bucket
          game before its one-second budget was even armed.  With [Some n],
          when the product of the initial set sizes over all [FN] keys of a
          side exceeds [n], every key of that side starts from the default term
          alone and gains terms only by refinement.  [None] (the default) keeps
          the full sets.  The product is taken over the side, not per clause,
          so it over-approximates what one clause multiplies.  Which initial
          strategy is proposed never decides an answer: every verdict comes
          from checking the strategy then current, and a strategy with fewer
          terms is checked by the same query. *)
  demonic_fallback_on_undecided_check : bool; [@default false]
      (** When a side's strategy check times out and the side's strategy
          gives some key more than one term, ask the demonic question before
          the timeout is handled: the same check with the side's strategy
          restricted to ONE term per key (one copy of the term product, no
          alternatives), for at most [demonic_fallback_max_copies] copies,
          each at [demonic_fallback_timeout] seconds.  The ordinary check is
          angelic: a counter-play must refute every alternative at once,
          which can need one long play per alternative, while a copy is
          refuted by one play against one term choice.  The first copy whose
          check returns a counter-play refines the opponent from it, as an
          ordinary counter-play does, and the turn passes to the opponent; if
          none does (every copy won, undecided, or its refinement left the
          opponent unchanged), the timeout is handled as without the field.
          A copy's counter-play is a real play against the restricted
          strategy, so it is used only to propose the opponent's candidates;
          a copy's win is a verdict only under
          [demonic_fallback_reads_wins].  Copies are asked in
          an order that puts each key's terms added since the side's
          previous check of a different strategy first, and a copy made only
          of terms that strategy already had last: that previous check
          refuted every such copy at once (against the side's rankings of
          that time), while a copy using a new term has never been checked.
          Off by default. *)
  demonic_fallback_reads_wins : demonic_copy_wins; [@default Not_read]
      (** Read only under [demonic_fallback_on_undecided_check]; see
          [demonic_copy_wins] for where the copies are asked.  Unless
          [Not_read], a restricted
          copy whose check is satisfiable (the copy wins) is handled as a win
          of the ordinary check: [f_ordinary]'s win arms decide it, so it is a
          verdict when every ranking is recorded by construction or proved
          transitive, and otherwise the copy-blind certification of the whole
          strategy decides, as for any win.  Sound because the answer rules
          hold for any term map whose sets are terms over the key's
          parameters, and a copy is the check of such a map (one term per
          key, the same rankings); the copy's win is the win of that
          single-term strategy, which is a strategy of the side.  [Not_read]:
          a copy's win is discarded and the fallback only proposes the
          opponent's candidates. *)
  demonic_fallback_max_copies : int; [@default 4]
      (** At most this many restricted copies per timed-out check under
          [demonic_fallback_on_undecided_check]. *)
  demonic_fallback_timeout : int; [@default 2]
      (** The budget, in seconds, of each restricted copy's check under
          [demonic_fallback_on_undecided_check]; it does not double. *)
  validate_verdicts : bool; [@default false]
      (** Translation validation of every verdict.  The rewrites the verdict
          path passes formulas through -- the simplifier and its negating
          form, the constraint problem's normalisation, the clausal forms and
          let elimination inside the CHC backend, and the backend's own
          reading and decoding -- are checked on the objects of this run
          instead of being trusted:
          - a win ([valid] of the checked side) is printed only when the CHC
            solver's solution, substituted into the check exactly as this
            solver built it and handed it to the backend, makes every formula
            of the check valid, asked of Z3 on that formula's direct encoding;
          - a refutation of a side with no decision is printed only when the
            solver's derivation is checked node by node against the check's
            formulas (each node's conclusion forced by one formula once its
            premises hold, the root contradicting one), each step a question
            to Z3 on the direct encoding;
          - the transitivity proof of a ranking is asked without the
            simplifier, after the one exact rewrite that selects a [case]
            branch at a literal index;
          - the simplifications applied to the input before the reduction
            (the problem's own simplification, the dual's negations, the
            reduction's simplification and clausal form) are each checked to
            be an equivalence, predicates read as uninterpreted relations;
            one that is not shown equivalent makes every verdict of the run
            [unknown].
          A check that fails or is undecided turns the verdict into [unknown].
          Off by default; it can only replace a verdict by [unknown]. *)
  validate_verdicts_timeout_ms : int; [@default 5000]
      (** The budget of each Z3 question [validate_verdicts] asks. *)
  verbose : bool; [@default false]
}
[@@deriving yojson]

(* Each per-behaviour field, resolved against the umbrella: [Some b] is [b],
   [None] is [name_opponent_decisions].  The solver reads these and never the
   option fields directly, so the resolution rule is stated once. *)
let resolve cfg = function
  | Some b -> b
  | None -> cfg.name_opponent_decisions

let name_universals cfg = resolve cfg cfg.name_universals
let chain_pairs_from_play cfg = resolve cfg cfg.chain_pairs_from_play

let detect_unchanged_refinement cfg =
  resolve cfg cfg.detect_unchanged_refinement


module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  Or_error.(
    (* a list of constant constructors, so structural equality is defined *)
    (if
       Stdlib.(
         cfg.refine_interpolant_leaves = default_refine_interpolant_leaves)
     then Ok ()
     else
       error_string
         "MuStrat: refine_interpolant_leaves is read by no refinement yet \
          (the guards built from interpolants are not built); only the \
          default [Farkas_lra; Spacer_chc] is accepted")
    >>= fun () ->
    (match (cfg.refine_rankings, cfg.refine_terms) with
    | (Joint_guided | Joint_steered _), Terms_pcsat ->
        error_string
          "MuStrat: refine_rankings = Joint_guided / Joint_steered select \
           terms and are read only with refine_terms = Terms_select (the \
           joint form under the constraint solver is not built)"
    | Joint_steered k, _ when k < 1 ->
        error_string "MuStrat: refine_rankings = Joint_steered k needs k >= 1"
    | Joint_steered _, _ when not cfg.resynthesise_wf_rankings ->
        error_string
          "MuStrat: refine_rankings = Joint_steered records the pairs of the \
           steered play among those every later ranking must contain, which \
           only resynthesise_wf_rankings keeps"
    | (Separate | Joint_guided | Joint_steered _), _ -> Ok ())
    >>= fun () ->
    MuCLP.Optimizer.Config.load_ext_file cfg.optimizer >>= fun optimizer ->
    PCSPSolver.Config.load_ext_file cfg.chc_solver >>= fun chc_solver ->
    PCSPSolver.Config.load_ext_file cfg.backup_chc_solver
    >>= fun backup_chc_solver ->
    PCSPSolver.Config.load_ext_file cfg.pcsp_solver >>= fun pcsp_solver ->
    PCSPSolver.Config.load_ext_file cfg.pcsp_solver_determ
    >>= fun pcsp_solver_determ ->
    Preprocessing.Preprocessor.Config.load_ext_file cfg.refine_preprocessor
    >>= fun refine_preprocessor ->
    (match (cfg.refine_guards, cfg.refine_labels) with
    | Cav24_sound, Labels_spacer ->
        PCSPSolver.Config.load_ext_file cfg.refine_labels_spacer_solver
    | _ -> Ok cfg.refine_labels_spacer_solver)
    >>= fun refine_labels_spacer_solver ->
    (match cfg.empty_strategy_chc_solver with
    | None -> Ok None
    | Some f -> PCSPSolver.Config.load_ext_file f >>| Option.some)
    >>= fun empty_strategy_chc_solver ->
    (match cfg.strategy_free_race_solver with
    | None -> Ok None
    | Some f -> PCSPSolver.Config.load_ext_file f >>| Option.some)
    >>= fun strategy_free_race_solver ->
    PCSPSolver.Config.load_ext_file cfg.reask_inline_chc_solver
    >>= fun reask_inline_chc_solver ->
    Ok
      {
        cfg with
        optimizer;
        chc_solver;
        backup_chc_solver;
        pcsp_solver;
        pcsp_solver_determ;
        refine_preprocessor;
        refine_labels_spacer_solver;
        empty_strategy_chc_solver;
        strategy_free_race_solver;
        reask_inline_chc_solver;
      })

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "MuStrat"
  let instantiate = instantiate_ext_files
end)
