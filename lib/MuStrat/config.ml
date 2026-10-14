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

type t = {
  optimizer : MuCLP.Optimizer.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/muval/optimizer/enable.json"]
  chc_solver : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/gspacer_cex.json"]
  backup_chc_solver : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/spacer_cex.json"]
  pcsp_solver : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/pcsat_wopp_tbq_ar_fixpoint.json"]
  pcsp_solver_determ : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/strat_synth_determ_forward.json"]
  determinize : bool; [@default false]
  check_problem : bool; [@default false]
  output_yes_no : bool; [@default false]
  name_opponent_decisions : bool; [@default false]
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
  resynthesise_only_on_new_pairs : bool; [@default false]
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
          field adds no answer rule.  Off, as before the field existed. *)
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
          as before the field existed. *)
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
  split_mixed_refinements : bool; [@default false]
      (** Read only when [select_skolem_terms] is on.  A refinement problem
          whose unknowns are Skolem keys ([FN]) together with ranking copies
          ([WF]/[DWF]) is not a pure existential, so model-guided selection
          does not apply to it and the constraint solver solves the whole
          problem, returning one template term per Skolem copy (a copy-blind
          counter-play's refinement added 13 to 19 terms for one key this way,
          where selection added one to four).  With this on, such a problem is
          split into the formulas that mention a ranking copy and the rest,
          provided the two share no unknown; the rest is solved by selection
          and the ranking part by the constraint solver, and the two
          solutions are joined.  Sharing no unknown, a solution of each part
          is a solution of the whole, so the join solves the problem asked;
          when selection does not apply to the rest, or the ranking part is
          not solved, the whole problem goes to the constraint solver as
          without the field. *)
  detect_unchanged_refinement : bool option; [@default None]
      (** Treat a refinement whose strategy is unchanged -- compared on the
          simplified first-order form, so that joining a ranking already present
          counts as no change -- as a failed refinement.  What a failed
          refinement then means is decided by [pass_turn_on_no_refinement]; with
          this on and that off, an unchanged refinement is read as a losing
          answer, as any failed refinement is.  [None] follows
          [name_opponent_decisions]. *)
  pass_turn_on_no_refinement : bool option; [@default None]
      (** On a failed refinement, pass the turn to the other side instead of
          answering [invalid], and answer [unknown] after two consecutive turns
          (one per side) on which neither refinement succeeded.  Off, a failed
          refinement is read as a losing answer for the checked side, which is
          exact only when a refutation cannot consist solely of steps the named
          encoding assumed covered.  [None] follows
          [name_opponent_decisions]. *)
  chc_timeout_policy : chc_timeout_policy; [@default Global_doubling]
      (** See [chc_timeout_policy].  Absent, the check is scheduled as it was
          before the field existed. *)
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
  name_term_alternatives : bool; [@default false]
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
  miniscope_term_alternatives : bool; [@default false]
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
  select_skolem_terms : bool; [@default false]
      (** When a refinement problem is a pure existential over its Skolem
          unknowns -- every unknown of kind [FN], each universal defined by a
          nullary Skolem constant, and the opponent's key copies applied only
          positively, each unknown once -- solve it from one Z3 model by
          model-guided term selection (Farzan and Kincaid, IJCAI 2016) instead
          of calling [pcsp_solver], and check the result valid before using it.
          Any other problem, or a selection whose check fails, still goes to
          [pcsp_solver].  The refined strategy is checked by the same strategy
          check as before, so this changes which strategies are proposed and
          never how an answer is decided.  Off, every refinement goes to
          [pcsp_solver], as before the field existed. *)
  select_skolem_guards : bool; [@default false]
      (** Read only when [select_skolem_terms] is on.  The copies of one
          opponent key in a refinement problem each get their own function
          from the selection, and each is added to that key's term set.  On,
          the copies whose selected terms differ are combined into one guarded
          definition [ite(g_1, t_1, ite(g_2, t_2, .. t_m))], the guards
          separating the argument points at which each term was selected (a
          threshold on one parameter where one exists, else a linear
          separator from a small Z3 query); copies whose terms agree share one
          branch.  The combined definition replaces the copies' functions only
          when the problem, with it substituted for every copy, passes the
          same validity check as the ungrouped solution; otherwise, or when a
          group's points cannot be separated (two copies selected at one
          argument point with different terms), the ungrouped solution is
          used unchanged.  The strategy check is unchanged, so this changes
          which strategy is proposed and never how an answer is decided.
          Off, the ungrouped solution is used, as before the field existed. *)
  select_prefer_bound : bool; [@default false]
      (** Read only when [select_skolem_terms] is on.  The published
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
          ends, which [select_skolem_guards] then combines.  The strategy check
          is unchanged, so this changes which strategy is proposed and never
          how an answer is decided. *)
  counter_plays_per_check : int; [@default 1]
      (** How many counter-plays one failed strategy check hands to the
          opponent's ranking refinement.  At 1 (the default, and any value
          below it) the refinement learns from the single derivation the CHC
          solver returns, as before the field existed.  At [k > 1], and only
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
  require_transitive_rankings : bool; [@default false]
      (** Accept a won strategy check as an answer only when Z3 proves every
          ranking the checked side substitutes transitive.  Each ranking is a
          finite union of well-founded pieces, so it is disjunctively
          well-founded, and a transitive disjunctively well-founded relation is
          well-founded (Ramsey's theorem).  With well-founded rankings a won
          check is a sound answer; with a merely disjunctively well-founded one
          the reduced check can be satisfied by choices that read the
          remembered copy of the state, which an invalid query can pass.  A win
          whose rankings are not proved transitive is treated as inconclusive:
          the turn passes with both strategies unchanged, and two inconclusive
          or stalled turns in a row answer [unknown].  Off, every won check is
          an answer, as before the field existed. *)
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
          [certify_wins_by_copy_blind]; a counter-play there refines the
          opponent, and a failed refinement from it passes the turn.  If that
          check yields neither, the timeout is handled as without the field.
          The copy-blind check makes every choice independent of the copy and
          is sometimes decided within the budget where the ordinary check is
          not.  On by default: it adds no answer rule, and on the POPL 2024
          games and nine smaller inputs it answered three files the default
          did not (one a game only the fixpoint-logic solver had answered) and
          lost none.  Off, a timeout is handled as before the field existed. *)
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
  certify_wins_by_copy_blind : bool; [@default true]
      (** Accept a won strategy check as an answer at once when Z3 proves every
          ranking the checked side substitutes transitive (a transitive
          disjunctively well-founded relation is well-founded, and a win with
          well-founded rankings is sound); otherwise check the same strategies
          again with [copy_blind_choices]'s encoding for that one check and let
          it decide.  So a win costs one extra check only when a ranking is not
          proved transitive, and the copy-blind restriction applies only then.
          On by default: without it the reduced check can be won by a prover
          whose choices read the copy, and an invalid query was answered
          [valid] that way.  On the POPL 2024 games and nine smaller inputs it
          lost one answer the unguarded check gave.  Off, every won check is an
          answer, as before the field existed. *)
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
          strategy, so it is used only to propose the opponent's candidates:
          a copy's answer is never a verdict, and every answer still comes
          from a check of the whole term-set strategy.  Copies are asked in
          an order that puts each key's terms added since the side's
          previous check of a different strategy first, and a copy made only
          of terms that strategy already had last: that previous check
          refuted every such copy at once (against the side's rankings of
          that time), while a copy using a new term has never been checked.
          Off by default. *)
  demonic_fallback_max_copies : int; [@default 4]
      (** At most this many restricted copies per timed-out check under
          [demonic_fallback_on_undecided_check]. *)
  demonic_fallback_timeout : int; [@default 2]
      (** The budget, in seconds, of each restricted copy's check under
          [demonic_fallback_on_undecided_check]; it does not double. *)
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

let pass_turn_on_no_refinement cfg = resolve cfg cfg.pass_turn_on_no_refinement

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  Or_error.(
    MuCLP.Optimizer.Config.load_ext_file cfg.optimizer >>= fun optimizer ->
    PCSPSolver.Config.load_ext_file cfg.chc_solver >>= fun chc_solver ->
    PCSPSolver.Config.load_ext_file cfg.backup_chc_solver
    >>= fun backup_chc_solver ->
    PCSPSolver.Config.load_ext_file cfg.pcsp_solver >>= fun pcsp_solver ->
    PCSPSolver.Config.load_ext_file cfg.pcsp_solver_determ
    >>= fun pcsp_solver_determ ->
    (match cfg.empty_strategy_chc_solver with
    | None -> Ok None
    | Some f -> PCSPSolver.Config.load_ext_file f >>| Option.some)
    >>= fun empty_strategy_chc_solver ->
    Ok
      {
        cfg with
        optimizer;
        chc_solver;
        backup_chc_solver;
        pcsp_solver;
        pcsp_solver_determ;
        empty_strategy_chc_solver;
      })

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "MuStrat"
  let instantiate = instantiate_ext_files
end)
