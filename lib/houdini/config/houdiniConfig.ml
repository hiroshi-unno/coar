(** Configuration of the Houdini pre-pass: when it runs against the CEGIS loop
    ([schedule]), which candidate atoms it offers ([candidates]) and how many
    ([quotas]), how its fixed point asks its questions ([questions]), and how
    the fixed point's final check is asked ([final_check]). The record is the
    [houdini] member of the validator's configuration; the qualifier generator
    whose atoms the pre-pass is also given stays the validator's
    [houdini_extracted_qualifiers], a configuration file of its own. A library
    of its own, so that the validator's configuration can hold it and the
    pre-pass's library can read it. *)

open Core

(** the copy's budget under [Parallel] *)
type parallel_budget =
  | Unbounded
      (** the copy's pre-pass has no budget of its own: it runs until it ends or
          the process it was forked from ends. The copy watches its parent and
          kills its own process group when the parent dies, so an outer time
          limit (a [timeout] around the run) bounds it, and the solver itself
          knows no overall time limit to size a budget by. The pre-pass only
          shrinks a finite candidate set, so without an outer limit it still
          ends. Costs one core and the copy's memory for as long as it runs. *)
  | Bounded of {
      budget_ms : int option; [@default None]
          (** the copy's pre-pass's budget; [None]: [budget_ms] of the pre-pass
              (and no budget when that is [None]) *)
    }
[@@deriving yojson]

(** When the pre-pass runs against the CEGIS loop. *)
type schedule =
  | Off  (** never *)
  | In_first_validation
      (** before the first candidate is checked, inside the first validation:
          the Houdini-style fixed point of the candidate atoms the input
          declares ([houdini_candidate]) is reported only when it satisfies
          every clause, and otherwise the round goes on as it would have *)
  | Before_synthesis of {
      after_ms : int option; [@default None]
          (** run the pre-pass lazily: [Some t] moves it from before the first
              round to the first round boundary at which at least [t]
              milliseconds of wall-clock time have passed since the
              coordinator's loop started. Contract:
              - [None]: exactly the eager behaviour above (before the first
                synthesis, at most once);
              - [Some t]: nothing is asked before the first round; at a later
                round boundary the coordinator asks
                [houdini_at_round_boundary ~elapsed_s], which runs the pre-pass
                iff [elapsed_s] is at least [t] milliseconds and it has not run
                in this solve, so it runs at most once; its outcome is used as
                the eager one's is (a solution is the answer; otherwise, with
                [feedback_counterexamples], its counterexamples are added and
                processed by the phases after validation before the next
                synthesis; otherwise the round goes on as it would have);
              - a problem answered before [t] never runs the pre-pass;
              - the pre-pass inside the first validation ([in_first_validation])
                is not moved: it still runs there, and once it has run the lazy
                pre-pass does not. The reason: the pre-pass with generated
                candidates spends up to [budget_ms] before CEGIS starts, which a
                problem CEGIS answers quickly pays for nothing; run after [t],
                it is paid only by problems that CEGIS has not answered by then.
          *)
      in_first_validation : bool; [@default false]
          (** also run the pre-pass inside the first validation, as
              [In_first_validation] does; it runs there only when the pre-pass
              has not run before, so beside the eager form it acts only when
              that form did not run *)
    }
      (** run the pre-pass once before the first synthesis: the coordinator asks
          [houdini_before_synthesis] before the first round, answers at once
          when the fixed point satisfies every clause, and otherwise starts the
          loop as it would have -- so a first candidate that the declared atoms
          already give does not wait for a synthesis *)
  | Parallel of {
      budget : parallel_budget;
          [@default
            Common.Util.config_default parallel_budget_of_yojson
              {|["Unbounded"]|}]
    }
      (** run the pre-pass in a forked copy of the process at the point where
          [Before_synthesis] would run it, concurrently with the loop, which
          starts at once as if the pre-pass had found nothing. The first to
          finish wins, and the winner is always a run the sequential mode could
          make:
          - the loop answers first: the copy is killed;
          - the copy's fixed point passes its final check (within [budget]): the
            copy becomes the run, answers [sat] with it, and the process exits
            with the copy's status, printing nothing more;
          - it fails within [budget_ms] (the sequential budget) and
            [feedback_counterexamples] is on: the copy becomes the run with the
            counterexamples added, exactly as the sequential pre-pass would have
            left it, the loop's progress meanwhile discarded (the sequential
            mode would not have had it either);
          - otherwise (it fails later, or spends its budget): the copy leaves
            and the loop goes on. The copy cannot send its result back instead
            of taking over: a solution or an example is a term of the
            extensible-variant term language, which does not survive [Marshal].
            The pre-pass inside the first validation is not run in this mode.
            When the copy cannot be forked (a process with a domain), the copy's
            pre-pass runs in the process before the loop, sequentially. *)
[@@deriving yojson]

(** how a sequence-existential question of the Houdini fixed point is asked
    ([questions.mode]) *)
type question_mode =
  | Plain_first
  | Switch
  | Dovetail of { start_ms : int [@default 500]  (** the first slice *) }
  | Race
[@@deriving yojson]

(** the inclusion family's second round *)
type second_round =
  | No_second_round  (** one round *)
  | Second_round of {
      budget_ms : int option; [@default None]
          (** round 2's own wall-clock budget; [None]: [budget_ms] of the
              pre-pass (and no budget when that is [None]) *)
    }
      (** on by default, with both inclusion counts at 24, for the reason given
          at [candidates.relation_inclusions]; the second round is what keeps
          the inclusions from costing the inputs the pre-pass answers without
          them. With [true], [candidates.relation_inclusions] positive and
          [quotas.inclusion] positive, the pre-pass runs in up to two rounds
          instead of one ([HoudiniCandidates.rounds]):
          - round 1 is the pre-pass with no inclusion generated: the same
            candidates, in the same order, under the same [budget_ms], as with
            [candidates.relation_inclusions = 0]; a fixed point that passes the
            final check is the outcome and nothing else is asked;
          - only when round 1's fixed point fails the final check (it has
            counterexamples and the budget was not spent), round 2 runs the
            fixed point from the FULL round-1 candidate set (not its survivors)
            plus the inclusions -- the pre-pass this switch off would run --
            under a fresh budget
            ([candidates.inclusions.second_round.budget_ms], else [budget_ms]);
            its outcome replaces round 1's, so round 1's counterexamples are
            dropped and only round 2's are fed back under
            [feedback_counterexamples];
          - when round 1 spends its budget, or has nothing to try, round 2 does
            not run (a superset of the candidates would spend it too). Each
            round's outcome is the ordinary final check of an inductive
            conjunction, so soundness is that of one round. Why: an inclusion,
            once offered, is a hypothesis of every inductive question until a
            pass refutes it, and on inputs answered from the pre-pass alone
            those extra hypotheses turned a few questions into per-question
            timeouts, each dropping an atom of the solution; while an atom
            inductive only relative to an inclusion needs the full candidate set
            beside the inclusion, which a round started from round 1's survivors
            would no longer hold. Cost: up to two budgets on an input both
            rounds fail. With [false] (or either count [0]) the questions asked
            are exactly the one-round pre-pass's. *)
[@@deriving yojson]

type inclusions = {
  skip_constructor_equations : bool; [@default false]
      (** with [true] (and [candidates.frame_equations] positive), an inclusion
          built from a definition whose inlined body is a constructor equation
          over the varied first formal is not offered when the frame family
          offers the equation it is equivalent to
          ([HoudiniCandidates.constructor_equation_body] states the test and the
          equivalence). On a Rust-derived loop such relations ([h2 = mut a h1])
          were 330 of the 336 inclusions offered, each equivalent to an equation
          [t1 = t2] and each one more question per pass of the fixed point. The
          quota [quotas.inclusion] then goes to the remaining inclusions. *)
  second_round : second_round;
      [@default
        Common.Util.config_default second_round_of_yojson
          {|["Second_round", {}]|}]
}
[@@deriving yojson]

type candidates = {
  defined_body_atoms : int; [@default 24]
      (** give the pre-pass the atoms of the input's non-recursive Bool
          definitions (a contract's pre- or postcondition, say) instantiated at
          the terms the unknown's parameters reach, at most this many per
          unknown -- the enumeration the array template's [defined_body_quals]
          makes, called with this limit. [0]: none; the default 24 is the
          measured setting of the generated classes, which are on together (see
          [houdini_extracted_qualifiers]). *)
  rec_fun_apps : int; [@default 24]
      (** give the pre-pass the applications of the input's recursive
          definitions ([define-fun-rec]) at the terms the unknown's parameters
          reach -- [x = f(t1, ..., tn)] for an integer- or real-valued [f],
          [f(t1, ..., tn)] for a Bool-valued one -- at most this many per
          unknown: the enumeration the array template's [rec_fun_app_quals]
          makes, called with this limit. Quantifier-free, so under
          [quotas.candidates]. [0]: none. The default 24 makes a loop whose
          invariant states a counted recursive function's value answer in about
          25 s where it timed out at 120 s without, and costs nothing measurable
          on inputs without such definitions *)
  frame_equations : int; [@default 24]
      (** offer the pre-pass at most this many equations [t1 = t2] between terms
          of one sort that two different parameters of an unknown reach
          ([HoudiniCandidates.frame_equations]); [0]: none *)
  contract_memberships : int; [@default 24]
      (** offer at most this many memberships of reached terms in the Boolean
          relations an unknown carries and in the input's non-recursive Boolean
          definitions ([HoudiniCandidates.memberships]); [0]: none *)
  oriented_inequalities : int; [@default 96]
      (** offer at most this many sign facts, orders and difference bounds over
          the integer terms an unknown reaches
          ([HoudiniCandidates.inequalities]); [0]: none *)
  quantified_facts : int; [@default 24]
      (** offer at most this many of the problem's own quantified subformulas
          instantiated at the terms an unknown reaches
          ([HoudiniCandidates.quantified_facts]); [0]: none *)
  quantified_facts_frame_only : bool; [@default true]
      (** with [candidates.quantified_facts] positive, each input fact the
          family instantiates that has a free variable of an opaque sort (a sort
          variable, an uninterpreted sort, a datatype; not an integer or a
          sequence, whose facts are ranges over a moving counter) some term
          reached from the unknown's frame parameters has (the parameters every
          loop of the unknown passes on unchanged,
          [HoudiniCandidates.frame_positions]) is instantiated with those terms
          only, in place of its instances of before; the facts instantiated are
          the same ([quantified_facts ~frame]). A precondition over a function's
          arguments stays true over a loop that keeps them, while its instances
          at the moving values were each asked, not inductive, and often left
          undecided at the question's whole budget, and the instance at the kept
          values could fall outside the instance limit. Changes only which
          candidates are offered: can lose an answer, never make one wrong. *)
  quantified_facts_closed_beside : bool; [@default true]
      (** with [candidates.quantified_facts] positive, an atom of the family
          with no free term variable (a sentence the input states, such as one
          a preprocessing step dropped as valid and the input's record still
          holds) does not count against [candidates.quantified_facts] nor
          [quotas.quantified]: it is offered beside them, together with the
          open atoms it would have displaced from the limit
          ([HoudiniCandidates.quantified_facts_split]). Every atom offered with
          the switch off is still offered; only candidates are added, so this
          cannot make an answer wrong. Why: such a sentence is small, ranked
          ahead of the open facts, and took the last slot from an atom an
          answer needed. [false]: closed atoms compete inside the limit, as
          before. *)
  relation_inclusions : int; [@default 24]
      (** on by default (24), with [quotas.inclusion = 24] and
          [candidates.inclusions.second_round]: together they answered 47 of 105
          Rust-derived inputs where the configuration without them answered 40,
          losing none and contradicting no answer. Offer at most this many
          inclusions [forall x. R(t1, x) => R(t2, x)] between two reached terms
          of a relation's first argument, for the Boolean relations an unknown
          carries and the input's non-recursive Boolean definitions of two or
          more formals ([HoudiniCandidates.inclusions]); being quantified, they
          fall under [quotas.quantified] when that is positive and
          [quotas.inclusion] is [0]; [0]: none *)
  guarded_inclusions : int; [@default 24]
      (** offer at most this many inclusions guarded by a range the input
          states for a bound integer variable
          ([forall x. g(x) /\ R(t1, x) => R(t2, x)], with [g] from
          [HoudiniCandidates.range_guards], at most four ranges, the smallest
          first; [HoudiniCandidates.guarded_inclusions]), as a family of their
          own with this quota, generated wherever [relation_inclusions] is
          (round 2 under [inclusions.second_round]). When every step of a
          loop states the inclusion only inside the range (a frontend that
          guards each quantified machine integer by its type's range), the
          unguarded inclusion is not inductive and the guarded one is. The
          family is empty unless the input bounds an integer variable by
          constants, and the default chains of MuVal and MuStrat turn the
          Houdini pre-pass off, so the quota acts only where such a range
          exists. [0]: none *)
  inclusions : inclusions;
      [@default Common.Util.config_default inclusions_of_yojson "{}"]
      (** how the inclusions are offered *)
  exists_memberships : int; [@default 24]
      (** offer at most this many existential memberships
          [exists t. r[.., t, ..]] and [exists t. r[.., t, ..] /\ len t + x = y]
          for a Boolean relation an unknown carries whose index sorts are all
          reached but one, a sequence sort
          ([HoudiniCandidates.exists_memberships]): the history a loop keeps,
          which no term over the parameters denotes. They have a quota of their
          own of the same size, outside [quotas.candidates], [quotas.quantified]
          and the inclusions' quota, as the inclusions do with
          [quotas.inclusion]: the atoms the other classes keep are exactly those
          they keep with this family off. Their questions bind a sequence
          existentially, which [questions.seq_instantiation] is for. [0]: none
      *)
  array_pair_memberships : bool; [@default true]
      (** with [candidates.exists_memberships], the family also takes as the
          history's sort a single-constructor datatype of exactly an
          [Int]-indexed array and an [Int] (the array-plus-length encoding of a
          sequence that Rust-derived inputs over Creusot's [Seq] use):
          [exists a l. r[.., c(a, l), ..]] and
          [exists a l. r[.., c(a, l), ..] /\ l + x = y]. Without it only a
          sequence sort is taken, as before. A candidate atom like any other: it
          is kept only when the fixed point proves it, and the fixed point is
          reported only after the ordinary check against every clause. *)
  guarded_frame_equations : int; [@default 48]
      (** offer at most this many guarded frame equations [x = y => u = v]
          ([HoudiniCandidates.guarded_frame_equations]): a frame equation
          between two parameters' reached terms that holds only until a counter
          reaches its bound ([n = e.1 => s.0 = e.0]: no iteration yet, so the
          inner state is untouched). They have a quota of their own of the same
          size, after the existential memberships', so the atoms the other
          classes keep are those they keep with this family off. [0]: none *)
  empty_guarded_frames : int; [@default 24]
      (** offer at most this many empty-guarded frame equations
          [len s = 0 => u = v] ([HoudiniCandidates.empty_guarded_frames]): a
          frame equation between two parameters' reached terms that holds while
          a reached sequence, the history a loop keeps, is still empty
          ([len sk = 0 => m.0 = s.0]: nothing drained yet, so the inner iterator
          is the one the adapter was built from). They have a quota of their own
          of the same size, after the guarded frame equations', so the atoms the
          other classes keep are those they keep with this family off. Adding
          candidates can only change which fixed point is found, and the fixed
          point is reported only after the ordinary check against every clause.
          [0]: none *)
  last_element_equations : int; [@default 24]
      (** offer at most this many equations [v = s[len t]] between a reached
          term and the entry of a reached sequence at the length of another
          ([HoudiniCandidates.last_element_equations]): the current value a loop
          also keeps as the last entry of a ghost history ([g = fs[len s]], the
          closure state beside the history of produced items), which no other
          family offers. On its own quota, after every other family, so it takes
          no place from them and adds at most this many questions per pass. [0]:
          none *)
  length_sums : int; [@default 24]
      (** offer at most this many equations [len s + x = t] between a reached
          sequence's length, a shift [x] (zero or a reached integer term) and a
          target [t] (a reached integer term or another reached sequence's
          length) -- the count a loop keeps between the items it has collected
          and an iterator's positions ([len out + a.0 = b.0])
          ([HoudiniCandidates.length_sums]). Quantifier-free, so under
          [quotas.candidates]. [0]: none *)
  affine_elements : int; [@default 24]
      (** offer at most this many universals
          [forall i. 0 <= i < len s => s[i] = t + i] for a reached sequence [s]
          of integers and [t] zero or a reached integer term -- the content of a
          sequence collected from a counting range
          ([HoudiniCandidates.affine_elements]). Being quantified, they fall
          under [quotas.quantified] when that is positive and [quotas.affine] is
          [0]; [0]: none *)
  prefix_elements : int; [@default 24]
      (** offer at most this many prefix universals
          [forall i. 0 <= i < x => s[i] = c] for a reached sequence [s] of
          integers, a reached integer term [x] (another reached sequence's
          length included, never [len s]) and [c] one of the four integer
          literals of the input smallest in absolute value
          ([HoudiniCandidates.prefix_elements]): the part of a sequence a loop
          has already overwritten, below its position. They have a quota of
          their own of the same size, after the empty-guarded frame equations',
          so the atoms the other classes keep are those they keep with this
          family off. [0]: none *)
  guarded_orders : int; [@default 24]
      (** offer at most this many orders guarded by a sequence's emptiness,
          [len s = 0 \/ t1 <= t2], for a reached sequence [s] and two distinct
          reached integer terms ([HoudiniCandidates.guarded_orders]) -- the
          bound a loop keeps only once it has produced something
          ([len out = 0 \/ b.0 <= b.1]: an iterator that produced an item was
          not past its end), which an unguarded order cannot state when the
          empty case starts from an arbitrary range. Quantifier-free, so under
          [quotas.candidates] unless [quotas.counting] is positive. [0]: none *)
  three_term_equations : int; [@default 24]
      (** offer at most this many equations [x = y - z] between three distinct
          reached integer terms (sequence lengths included), one of [x = y - z]
          and [z = y - x] for each, the smallest first
          ([HoudiniCandidates.three_term_equations]): an exact count kept
          between a counter and two positions ([n = b.0 - it0.0]).
          Quantifier-free, so under [quotas.candidates]. [0]: none *)
  shifted_elements : int; [@default 24]
      (** offer at most this many universals
          [forall i. 0 <= i < len b => a[len c + i] = b[i]] for three pairwise
          distinct reached sequences of one sort whose element sort is one the
          problem's clauses build a sequence of by concatenation
          ([HoudiniCandidates.shifted_elements]): a sequence [a] that started
          as [c] and has had the items of a history [b] pushed onto it
          ([v[len v0 + i] = pushed[i]], an [extend] loop), which no other
          family states. On its own quota, after every other family (the
          contract memberships' included), so the atoms the other classes keep
          are those they keep with this family off; at most this many
          questions more per (clause, head atom) pair and pass. With [n]
          reached sequences of one sort the family builds [n (n-1) (n-2)]
          atoms before the cut. [0]: none *)
  affix_elements : int; [@default 0]
      (** offer at most this many universals stating that one reached
          sequence [b] is a prefix, [forall i. 0 <= i < len b => a[i] = b[i]],
          or a suffix, [forall i. 0 <= i < len b => a[len a - len b + i] =
          b[i]], of another reached sequence [a] of the same sort
          ([HoudiniCandidates.affix_elements]): the prefix half of
          [*v = *vec ++ produced] that the shifted elements leave out (an
          [extend] loop), and the rest of a sequence a loop consumes from its
          front (a slice iterator). On its own quota, after every other
          switched family's, so the atoms the other classes keep are those
          they keep with this family off. With [n] reached sequences of one sort the
          family builds [2 n (n-1)] atoms before the cut. [0]: none *)
  concat_equations : int; [@default 0]
      (** offer at most this many equations [a = c ++ b] between three
          pairwise distinct reached sequences of one sort whose element sort is
          one the problem's clauses build a sequence of by concatenation
          ([HoudiniCandidates.concat_equations]): the whole of
          [*v = *vec ++ produced] of an [extend] loop, quantifier-free, where
          the shifted and affix families state it pointwise. On its own quota,
          after the affix elements'. With [n] reached sequences of one sort the
          family builds [n (n-1) (n-2)] atoms before the cut. [0]: none *)
  constructor_cases : int; [@default 24]
      (** offer atoms inside the cases of a datatype with several constructors
          ([HoudiniCandidates.constructor_cases]), which the other families do
          not reach (their terms stop at such a datatype): for an opened view,
          in which every reached term [t] of the sort is replaced by the fields
          of one constructor [c], the frame, inequality, length-sum,
          affine-element, three-term, guarded-order and empty-guarded-frame
          families over the view, each atom guarded by the testers [is_c(t)] of
          the fields it mentions; and [is_c(t) => is_c(u)], [is_c(t) => e] for a
          frame equation [e] or an emptiness [len s = 0]. What it adds: an
          adapter that keeps its inner iterator in an option
          ([Fuse { iter: Option<I> }]) relates the contents of [s.iter] and
          [o.iter] as the inner [produces] relates its states, and without this
          family its unknown gets no atom about the items produced. Sound: the
          atoms are only candidates, which the pre-pass's questions keep or
          drop, and the tester guard keeps every selector application on a
          value of its own constructor. On its own quota after every other
          family, so the atoms the other families keep are those they keep with
          it off; at most this many atoms from the tester-only part and from
          each family over each view. It builds nothing for an unknown none of
          whose parameters reaches a datatype with several constructors (an
          input without such a datatype, or one whose unknowns carry only
          integers, sequences, arrays and records), so there it costs nothing
          and changes nothing. [0]: none *)
  drop_premise_atoms : bool; [@default true]
      (** leave out of the pre-pass's candidates a generated atom that every
          clause applying the unknown already has as a premise at each
          application ([HoudiniCandidates.premise_redundant]): a law of a
          universal the unknown carries, which the reader put into each such
          clause. It cannot change whether a clause holds, and cost a question
          per clause and pass and a hypothesis in every other question. *)
}
[@@deriving yojson]
(** the candidate families the pre-pass is offered beside the declared atoms (an
    [int] is the family's quota per unknown, [0]: none) *)

type quotas = {
  candidates : int; [@default 128]
      (** how many candidate atoms an unknown may carry into the pre-pass when
          atoms are generated (the two switches above); the declared atoms are
          always kept, and the generated ones fill the remainder, the smallest
          by [Formula.ast_size] first. The pre-pass asks, per pass, one question
          per remaining atom per (clause, head atom) pair, and makes at most one
          pass more than it has atoms, so the number of questions grows with the
          square of the cap in the worst case and linearly when most atoms go in
          the first pass, which is the common case (a generated atom that is not
          inductive fails there). The default 128 is the setting the generated
          classes were measured with together; it is bounded in time by
          [budget_ms] rather than by the square above, since a spent budget
          drops every atom not yet confirmed. Ignored when no atom is generated.
      *)
  membership : int; [@default 24]
      (** with a positive value, the contract memberships
          ([candidates.contract_memberships]) are taken out of
          [quotas.candidates] and given a quota of their own of this many, after
          every other family, in the generator's order (see
          [HoudiniCandidates.merge]'s [own_quotas]). Why: a membership of a
          three-place relation over a sequence ([r(e.0, sk, s.0)], the loop
          history of an adapter) is larger than the oriented inequalities over
          the same terms, so under one ranking by size the default 96
          inequalities fill the cap before it; an input whose invariant needs
          that membership then lost it, and lowering the inequality quota to
          make room cost another input the two inequalities it needs. Adding a
          family's own quota can only add questions; the fixed point is reported
          only after the ordinary check against every clause. [0]: the
          memberships rank with the other quantifier-free atoms, as before. *)
  quantified : int; [@default 24]
      (** with a positive value, the quantified generated atoms of an unknown
          are kept apart from [quotas.candidates]: at most this many of them,
          the smallest first, beside the cap rather than inside it (see
          [HoudiniCandidates.merge]). [0]: one ranking by size for all generated
          atoms, in which the quantified ones, being the largest, are the first
          a cap drops. *)
  inclusion : int; [@default 24]
      (** on by default (24), with [candidates.relation_inclusions = 24] and
          [candidates.inclusions.second_round], for the reason given at the
          first. With a positive value, the inclusions
          ([candidates.relation_inclusions]) have a quota of their own, outside
          both [quotas.candidates] and [quotas.quantified]: the atoms the other
          classes keep are exactly those they keep with the inclusions off, and
          at most this many inclusions, the smallest first, are added beside
          them ([HoudiniCandidates.merge]). Ranked with the other quantified
          atoms, the inclusions (small universals) took the whole quantified
          quota on Rust-derived loops and displaced the contract's pointwise
          facts that the pre-pass answered those inputs from. Generating them is
          inside [budget_ms] as every class is; but each atom added here is one
          more question per (clause, head atom) pair in each pass of the fixed
          point, so a quota costs fixed-point time in proportion to it, bounded
          only by the same budget. [0]: the inclusions are ranked with the other
          generated atoms. *)
  affine : int; [@default 24]
      (** with a positive value, the affine element universals
          ([candidates.affine_elements]) have a quota of their own outside both
          caps, as [quotas.inclusion] gives the inclusions: the atoms the other
          classes keep are exactly those kept with the family off, and at most
          this many affine universals, the smallest first, are added after them.
          [0]: ranked with the other generated atoms. *)
  counting : int; [@default 72]
      (** with a positive value, the length sums, the three-term equations and
          the guarded orders ([candidates.length_sums],
          [candidates.three_term_equations], [candidates.guarded_orders]) have a
          quota of their own outside both caps, with the contract of
          [quotas.inclusion]: the atoms the other classes keep are exactly those
          kept with these families off, and at most this many of theirs, the
          smallest first, are added after the inclusions and the affine
          universals. Ranked with the quantifier-free atoms under
          [quotas.candidates], they are larger than the sign facts and orders of
          the other families, and a needed three-term equation was cut by the
          cap before a question was asked about it. [0]: ranked with the other
          generated atoms. *)
}
[@@deriving yojson]
(** how many candidate atoms an unknown carries into the pre-pass, and the
    families kept on quotas of their own *)

(** the conjunction question of classic Houdini, asked before the per-atom
    questions *)
type drop_by_model =
  | No_drop_by_model  (** one question per atom *)
  | Drop_by_model of {
      solver_ms : int option; [@default None]
          (** with [questions.drop_by_model], [Some ms]: an atom the
              countermodel leaves undecided after substitution and
              simplification (an application of a recursive function such as a
              datatype's size, a quantifier over the model's arrays, an
              existential over a sequence) is asked of the solver with the
              model's values substituted, in a forked copy killed after [ms]
              (capped by what is left of the pre-pass's budget): unsatisfiable
              makes it false in the model, so it is dropped; its negation
              unsatisfiable makes it true. Why: on an iterator adapter's loop
              the atoms no substitution judged were left to their own clause
              questions, and four of those (existentials over the loop's history
              with a wrong length) took 31 s of a 41 s fixed point. Sound as the
              model drop is: an atom is dropped only when false in the
              countermodel *)
      quantified_aside : bool; [@default false]
          (** with [questions.drop_by_model], an atom that is not
              quantifier-free is never put in the conjunction question, only
              judged against each of its countermodels (dropped when false in
              one) and otherwise left to its own question. Why: with
              [questions.drop_by_model.solver_ms] such atoms (existentials over
              a loop's history) are judged true and stay in the conjunction, and
              a conjunction holding dozens of sequence existentials was a
              question that did not return within the pre-pass's budget, where
              the same conjunction without them was proved or refuted in a
              fraction of a second *)
      batch_ms : int option; [@default None]
          (** with [questions.drop_by_model], [Some ms]: once per countermodel,
              the atoms its substitution leaves undecided (quantified atoms,
              applications of a recursive function such as a datatype's size,
              reads of a relation at elements of an uninterpreted sort) are
              judged all together in one forked copy killed after [ms] (capped
              by the pre-pass's budget), each asked of Z3 with the model's
              values substituted and at most 500 ms: unsatisfiable makes it
              false in the model, its negation unsatisfiable true; an atom the
              copy does not decide, or a killed copy, leaves it to its own
              question. Why: on a fold loop the countermodel left 68-80 of 136
              atoms unjudged, and [questions.drop_by_model.solver_ms] paid a
              fork per atom. Sound as the model drop is: an atom is dropped only
              when false in the countermodel *)
      conjunction_ms : int option; [@default Some 6000]
          (** with [questions.drop_by_model] and [questions.seq_question_ms],
              [Some ms]: a conjunction question's witness-instantiation route is
              capped at [ms] instead of [questions.seq_question_ms]. Why: one
              conjunction question decides many atoms, and cut short it leaves
              every held atom to its own question. On an iterator adapter's loop
              (skip) a conjunction of 51 atoms was proved by the route in about
              2 s, which a 1 s cap cut, and the fixed point then ran past the
              pre-pass's budget; on a generic fold an uncapped conjunction
              question ran 23 s and proved nothing. [None]: the same cap as
              every other question *)
      conjunction_plain_first_ms : int option; [@default None]
          (** with [questions.drop_by_model], [Some ms]: a conjunction
              question's plain question (asked before the witness-instantiation
              route) gets [ms] in place of [questions.seq_plain_first_ms]. Why:
              on a generic fold a conjunction of 11 atoms was left undecided by
              the plain question at its 1 s, then the route's ladder spent 11 s
              building forms without a proof, and the unrewritten question asked
              after it found the countermodel in 0.6 s; a conjunction question
              is mostly refuted, and its model is what drops atoms *)
    }
      (** in each pass of the pre-pass's fixed point, before asking about one
          atom at a time, ask a (clause, head atom) pair once with the
          conjunction of every atom still held as the head (classic Houdini):
          when that question is proved every atom is kept without a question of
          its own; when it is refuted, each atom that the countermodel makes
          [false] (substituted and simplified; an atom the simplifier leaves
          undecided, such as one binding a sequence existentially, is not
          judged) is dropped, and the conjunction of the rest is asked again,
          until a question is proved, undecided, or drops nothing; the atoms
          still held then get the per-atom questions as before. Why: the
          pre-pass asked one question per atom, and with some 250 generated
          atoms over a large clause (an iterator adapter's loop) its 30 s budget
          ran out in the first clause at about 0.8 s a question. An atom false
          in a model of the clause's body under the current candidate is one its
          per-atom question would refute with that same model, so when every
          question decides the fixed point is the one without the switch; an
          unsound countermodel (a weakened question's) can only drop more, and
          the fixed point is reported only after the ordinary check against
          every clause, so the switch can lose an answer and never produce a
          wrong one *)
[@@deriving yojson]

type memo = {
  questions : bool; [@default true]
      (** inside one pre-pass, a question printed exactly as one already decided
          gets the same answer without being asked again (only decided answers
          are kept). Why: in each pass of the fixed point the clauses whose body
          does not apply the unknown, and the step clauses whose hypothesis the
          previous pass left unchanged, ask the same questions again; on a fold
          loop 265 of 365 questions were textual repeats of earlier ones (8 s of
          24 s). The same formula under the same problem has the same validity,
          so the fixed point is the one without the field. *)
  before_simplify : bool; [@default true]
      (** in the pre-pass's fixed point, a question printed exactly as one
          already decided in the same fixed point, before it is simplified, gets
          that answer (and its countermodel) without being simplified or asked.
          The same formula simplifies to the same question, so the answers and
          the fixed point are the ones without the field. Why:
          [questions.memo.questions] looks a question up only after simplifying
          it, which on a fold loop was most of the cost. On by default, being
          exact *)
}
[@@deriving yojson]
(** the in-memory record of answers inside one pre-pass *)

type questions = {
  seq_instantiation : bool; [@default true]
      (** inside the pre-pass (its fixed point and the final check of the fixed
          point), ask a question that binds a sequence existentially -- a
          positive [exists] or a negative [forall] over a variable of sequence
          sort, which an existential candidate atom such as
          [exists t. len t + n = m /\ r(a, t, b)] puts there in a head and in a
          body -- through [SeqInstantiation.decide_clause]: first its
          instantiated forms (each positive sequence existential replaced by a
          term the clause builds, [x0 ++ x1] for a chained pair of applications
          among them, each positive universal skolemised), each of which implies
          the question, so a proof of one ends it as valid; then the pinned
          refuters, whose models are models of the question's own negation; and
          only then the question asked without the switch, whose answer is
          returned as it is. So the switch can only prove valid what was
          otherwise undecided: a question it answers valid is valid, a
          counterexample it returns is one, and it never makes a fixed point
          that is not inductive look like one -- it cannot produce an [unsat],
          since the pre-pass reports only solutions. The witness instantiation
          is the one the zero-unknown verdict uses, with its switches set from
          the coordinator's [zero_unknown] record before the pre-pass (and so
          also for the read-back route afterwards). When off, every question is
          asked as before and those switches are left alone. *)
  mode : question_mode;
      [@default
        Common.Util.config_default question_mode_of_yojson {|["Switch"]|}]
      (** with [questions.seq_instantiation], how a sequence-existential
          question of the pre-pass's fixed point (a conjunction question of
          [questions.drop_by_model] or a per-atom one) is asked, between its two
          searches -- the plain, unrewritten question, which finds a
          countermodel or a proof, and the witness-instantiation route, asked
          for a proof only -- within the question's cap (the pre-pass's
          deadline, narrowed by [questions.seq_question_ms], or by
          [questions.drop_by_model.conjunction_ms] for a conjunction):
          - [Plain_first]: as before this field ([questions.seq_plain_first_ms],
            [questions.drop_by_model.conjunction_plain_first_ms], then the
            route);
          - [Switch]: the plain question for [questions.seq_plain_first_ms] (the
            cap when that is unset), then the route once for the rest of the
            cap;
          - [Dovetail]: the plain question and the route in turn, in slices
            doubling from [questions.mode.start_ms];
          - [Race]: both at once in two forked copies; the first decisive answer
            wins and the other copy is killed. In every mode the first decisive
            answer is taken: a countermodel or a proof from the plain question,
            a proof from the route. The final check is asked as without the
            field. *)
  seq_plain_first_ms : int option; [@default Some 1000]
      (** with [questions.seq_instantiation], a sequence-existential question of
          the pre-pass is first asked as the pre-pass asks every other question
          ([check_clause_nonparam_smt]: the clause's negation, its own forking
          and weakening switches included) under a budget of at most this many
          milliseconds, and goes to the witness instantiation only when that
          answer is neither a proof nor a counterexample. It is the question the
          pre-pass asks without [questions.seq_instantiation], so it decides
          nothing that route would not decide: a proof is an [unsat] of the
          negation and a counterexample a model of it. Why: the instantiation
          builds its forms in OCaml at 0.5-0.9 s a question, so on an input
          whose fixed point asks about a hundred such questions it spends the
          pre-pass's budget before the fixed point is reached, while most of
          those questions are decided by the plain question in milliseconds.
          [None]: the instantiation is asked first, as before *)
  seq_question_ms : int option; [@default Some 2000]
      (** with [questions.seq_instantiation], the witness-instantiation route of
          one sequence-existential question of the pre-pass's fixed point (its
          instantiated forms, its pinned and length-bounded refuters, the
          zero-unknown verdict's ladder, and the unrewritten question asked
          last) is given at most this many milliseconds: the pre-pass's deadline
          is narrowed to that for the question and restored after it, so every
          solver call on the route is given at most what is left, and once it is
          spent no further form is built or asked and the question is answered
          [`Timeout], as a question that ran out of the pre-pass's own budget
          is. A proof found before that is still a proof and a model still a
          counterexample, so the cap can only leave a question undecided, and
          its candidate atom is then dropped; the fixed point is still checked
          against every clause before it is reported. The final check's
          questions are not capped: one cut short there would reject the whole
          fixed point, not one atom, and send the pre-pass into another round.
          Why: the route asks dozens of solver questions of up to 10 s each, and
          on an input whose existential candidates it cannot prove it spent 5-19
          s on each of a handful of questions, so the fixed point ran past the
          pre-pass's budget and nothing was reported, while the questions the
          route did prove were proved within about 2 s. [None]: no cap but the
          pre-pass's own *)
  array_existentials : bool; [@default false]
      (** with [questions.seq_instantiation], a pre-pass question that binds an
          [Int]-indexed array existentially (a positive [exists] or a negative
          [forall]) takes the route a sequence-existential one takes: the plain
          question first under [questions.seq_plain_first_ms], then the witness
          instantiation, whose forms include the pointwise array witnesses. Each
          form implies its question, and a counterexample is still only a model
          of the negation, so the answers mean what the plain route's do. Why:
          the array-plus-length history of an iterator loop is such an
          existential, and the plain question leaves it undecided over arrays.
      *)
  atom_questions_prove_only : bool; [@default true]
      (** with [questions.seq_instantiation], a per-atom question of the
          pre-pass's fixed point that takes the witness-instantiation route
          builds no refuter (neither the pinned nor the length-bounded ones),
          and runs in a forked copy killed at the pre-pass's deadline (narrowed
          by [questions.seq_question_ms] when that is set): its atom is kept
          only when the question is proved, and a refutation drops it exactly as
          an undecided answer does, so a refuter can only cost time, and only
          the proof has to come back. A conjunction question of
          [questions.drop_by_model] and the final check keep their refuters,
          whose models those use. Why: building one length-bounded refuter, or
          the ladder's forms, is not a solver call, so no budget cuts it short,
          and on an iterator adapter's loop two refuter constructions took 6 and
          8.5 s, and one ladder's 10 s, of a fixed point the pre-pass's 30 s
          budget could not then hold *)
  memo : memo; [@default Common.Util.config_default memo_of_yojson "{}"]
  simplify_shared_once : bool; [@default true]
      (** in the pre-pass's fixed point, the disjuncts a clause shares between
          its questions (its pure part and the other atoms, as converted once by
          [questions.shared_conversion]) are simplified once per clause and
          pass, and each question is simplified from those and its own head
          ([Evaluator.simplify_with_leaf_cache]); the question is the one
          simplifying it whole gives, up to bound names. Why: each question is
          the whole clause with the current conjunction substituted, and
          simplifying the shared parts again for every atom was about 29 s of a
          fold loop's pre-pass (a quarter of it in Set.Poly), by a profiler. On
          by default, being exact up to bound names *)
  shared_body_session : bool; [@default true]
      (** in the pre-pass's fixed point, before a clause's question about a
          candidate head is asked, try to prove it against the clause's body
          held in one solver: per clause and pass the body's negation is
          simplified, the conjuncts [Z3interface.may_not_return] refuses are set
          aside, and the rest is converted and asserted once
          ([Z3interface.base_session_set]); each head's negation is then checked
          against it in a scope ([base_session_unsat]). An [unsat] proves the
          question valid -- the rest is implied by the body's negation, so
          [rest /\ ~head] unsatisfiable makes [body \/ head] valid -- and the
          question is not asked. Any other answer leaves the question to be
          asked as before, so the fixed point is the same whenever every
          question decides; what changes is that a valid atom's question, which
          converted and asserted the whole body (tens of conjuncts) every time,
          now converts one head. A head whose negation the solver may not return
          from is never tried here. *)
  atom_countermodel_drops : bool; [@default true]
      (** in the pre-pass's fixed point, the countermodel that refutes one
          atom's own question is also judged against the atoms of the same
          clause still to be asked in the pass, and every atom it makes false
          ([HoudiniByModel.judge]) is dropped without a question of its own. A
          question answered in a forked copy (with
          [questions.fixed_point_verdict_only] no model comes back) is judged in
          the copy, which sends back only the positions of the refuted atoms; a
          question answered in this process by a plain solver check is judged
          here. Sound for the same reason as [questions.drop_by_model]: within a
          pass the body of a clause's questions is fixed, so a model of
          [body /\ ~a] in which [b] is false is a model of [body /\ ~b], which
          refutes [b]'s own question. The judge is bound to the very formula
          asked (physical identity), so a model of a strengthened or rewritten
          form asked on the way is never read as one of the question. The fixed
          point is unchanged whenever every question decides; what changes is
          how many questions it takes. *)
  drop_by_model : drop_by_model;
      [@default
        Common.Util.config_default drop_by_model_of_yojson
          {|["Drop_by_model", {}]|}]
  skip_clause_after_timeout : bool; [@default false]
      (** in each pass of the pre-pass's fixed point, once a question about a
          clause has run out of its budget (a timeout, or a forked copy killed
          at its budget), ask nothing more about that clause in that pass: every
          atom still to be asked there, for any of its head atoms, counts as
          undecided and is dropped, exactly as a spent [budget_ms] drops it, and
          the pass goes on with the next clause. A later pass asks the clause
          again. Dropping atoms can only shrink the fixed point, which is
          reported only after the ordinary check against every clause, so this
          can lose an answer the pre-pass would have found and never produce a
          wrong one; it stops one clause whose questions do not return from
          spending the whole budget *)
  fixed_point_verdict_only : bool; [@default true]
      (** in the pre-pass's fixed point, a question answered satisfiable by a
          forked copy (the questions a solver may not return from are asked in
          one) is not asked again in this process for its model: the fixed point
          reads only whether the clause holds, so the question's answer is the
          copy's, with an empty model. The fixed point and the questions it asks
          are the same whenever the asking again would also have answered
          satisfiable; when it would not have, the atom is dropped either way,
          and only whether the question counts as timed out differs, which
          matters only with [questions.skip_clause_after_timeout]. The final
          check, which builds counterexamples from the models, asks again as
          before. What it saves is that second, in-process question, one per
          atom a forked question refutes. *)
  fork_fresh_context : bool; [@default false]
      (** a question of the pre-pass asked in a killed copy is asked there in a
          Z3 context made for it alone rather than the pooled one. The copy's
          answer is all that comes back, so the pooled context of this process
          is untouched either way. Why: a refutable conjunction question that a
          fresh z3 answers in 0.04-0.1 s, under every replay condition tried,
          was killed at 1 s in the copy *)
  weaken_unreturnable : bool; [@default true]
      (** inside the Houdini pre-pass's window only, ask a question that
          [may_not_return] refuses as [weaken_unreturnable_queries] does (the
          rest first; its [unsat] is the answer, a model of it only when every
          dropped conjunct is shown to hold under it) before it is asked in a
          killed copy. The pre-pass asks one question per (clause, candidate),
          and a loop clause carrying a callee's law as a universal over
          sequences makes each of them such a question: one input lost about
          forty of them, trivial ones such as [len v >= 0] among them, to the
          copy's 5 s kill, and the pre-pass spent its budget before reaching a
          fixed point. The weakened question is implied by the original, so this
          adds answers and never changes one. On by default. *)
  linear_subst : bool; [@default true]
      (** build each question of the pre-pass's fixed point with
          [Logic.Term.subst_rename_on_capture] instead of [Logic.Term.subst],
          and substitute the disjuncts a (clause, head atom) pair shares across
          its candidate atoms once per pass rather than once per atom. The
          question is the same formula up to the names of bound variables
          ([subst_rename_on_capture]'s contract, the clause and the candidate
          lambdas being beta-normal). [subst] reduces an application of an
          n-parameter candidate one argument at a time and renames the whole
          conjunction of candidate atoms at every step, so a question costs
          about n traversals of every candidate it mentions; here it costs one.
          On by default: the questions are the same up to bound names, in the
          same order. It draws fewer fresh names, which moves every later name
          and with it the loop's trajectory, and a pass that finishes sooner can
          ask questions a spent budget would not have; neither changes what is
          sound to report *)
  (* [true], with [questions.linear_subst]: the parts of a pre-pass question
         that every atom asked against one clause shares -- the clause's pure
         part and its other literals, substituted once per pass -- are also
         converted to the first-order form once, and each question's formula is
         assembled from the converted parts and the converted head.  The
         conversion maps a Boolean constant to the same constant and a
         disjunction to the disjunction of the converted disjuncts, so the
         assembled formula is the one converting the whole question gives, and
         it is simplified and asked exactly as before: the same questions in the
         same order.  On by default: converting the whole question again for
         every atom asked against one clause was most of a question's cost
         beside its simplification, and with the shared parts converted once a
         pass reached a given question in a quarter to three fifths of the
         time on the two inputs measured.
         Without [questions.linear_subst], or [false], each question is converted
         whole. *)
  shared_conversion : bool; [@default true]
}
[@@deriving yojson]
(** how the fixed point asks its questions *)

type final_check = {
  goals_only : bool; [@default true]
      (** the final check of the pre-pass's fixed point asks only the clauses
          with no unknown in the head. Why it is sound: the fixed point is
          returned only after a pass that changed nothing, under the very
          candidate it returns, and in such a pass every (clause, head
          application) question was proved valid for every atom held -- an atom
          whose question is refuted, undecided or left unasked is dropped, and a
          drop is a change -- so for every clause with an unknown in its head,
          [body => atom \/ rest] is valid for each atom of the candidate, hence
          for their conjunction, which is the clause. A clause with no head
          application is never asked in the fixed point, so it is still checked.
          Why: on a generic fold the final check spent 5-16 s re-proving,
          through the instantiation route, a clause the last pass had proved,
          and the pre-pass ran past its budget in one run of three *)
  by_pieces : bool; [@default true]
      (** in the final check of the pre-pass's fixed point, a clause whose
          question came back neither proved nor refuted is asked again by its
          pieces ([PCSatCommon.ClausePieces.of_clause]: the conjuncts of its
          negation normal form, a disjunction distributed within a bound), each
          with the question the check asks of a clause; when every piece is
          proved the clause holds, and otherwise the first answer stands. Exact:
          the clause is the conjunction of its pieces in every model, and only
          proofs are taken from them. Why: the goal clause of an iterator's
          [next] whose head is a conjunction of postconditions is left undecided
          whole while each [body => c] is decided at once; the zero-unknown
          verdict already asks such a clause by its pieces, and the pre-pass's
          fixed point is checked against the clauses before any resolution has
          split them. Asked within what is left of [budget_ms]. *)
  retry_ms : int option; [@default None]
      (** in the final check of the pre-pass's fixed point (the ordinary check
          of the fixed point against every clause), a clause whose question ran
          out of its budget (a timeout, or a forked copy killed at it) is asked
          once more: the same question, the negation of the clause with the
          fixed point substituted, in a forked copy killed after this many
          milliseconds and asked there with no solver timer
          ([PCSatCommon.ForkedQuery.valid_within]). Only its [unsat] is read,
          and the clause then holds; anything else keeps the timeout, so the
          outcome is the one without the field. The retry is not counted against
          [budget_ms], and a clause the check did not reach because that budget
          ran out is not retried. Sound: it can only add a proof that the clause
          is valid, and the fixed point is reported only when every clause was
          so shown. [None]: no retry. Why: on a Rust-derived input the fixed
          point holds the solution's atoms and its final check was decided in 1
          s on one run, while on others one clause's question was killed at the
          5 s cap of a quantified question and the pre-pass reported nothing.
          Off by default *)
  seq_axiom_first : bool; [@default true]
      (** in the pre-pass's final check of its fixed point, ask a clause that
          mentions a sequence first in the sequence-axiom form
          ([Z3interface.with_seq_axiom_fallback], under its process-wide
          budget), and read a proof there as the clause's validity; anything
          else asks the ordinary question as before (with
          [clause_check_seq_axiom_fallback] not asking the axiom form again).
          Why: the fixed point is a large conjunction over sequences, the native
          sequence theory left three of five final questions undecided at their
          whole budget (5-8 s each, killed copies), and the axiom form then
          proved each in about 0.2 s. Sound as the fallback is: an axiom proof
          is a proof. *)
}
[@@deriving yojson]
(** the final check of the fixed point *)

type t = {
  schedule : schedule;
      [@default
        Common.Util.config_default schedule_of_yojson {|["Parallel", {}]|}]
  budget_ms : int option; [@default Some 30000]
      (** a wall-clock budget, in milliseconds, for the whole pre-pass --
          generating its candidates and asking its questions, not the final
          check of its fixed point, which is the ordinary check of a first
          candidate. Each question is given at most what is left of it, and once
          it is spent no further question is asked: every atom not yet confirmed
          counts as undecided and is dropped, which empties the conjunctions, so
          the pre-pass reports that it has nothing to try and the round goes on
          as it would have. A spent budget therefore never changes an answer; it
          only bounds what the pre-pass costs. [None]: no budget beyond each
          question's own. *)
  feedback_counterexamples : bool; [@default false]
      (** when the pre-pass's fixed point is not a solution, add the
          counterexamples of its failed final check to the examples, as the
          counterexamples of a rejected candidate are added. They come from the
          ordinary check ([find_all_counterexamples]) with their derivations
          recorded, so they are sound examples; before the first synthesis they
          go through the phases that follow validation (the labeling and
          resolution) before the synthesizer sees them, and inside the first
          validation they join that round's counterexamples. When off, a fixed
          point that is not a solution leaves nothing behind *)
  declared_first : bool; [@default false]
      (** before the pre-pass proper, run it once over the declared candidate
          atoms alone ([PCSP.Params.candidate_atoms]; nothing generated), and
          answer with that fixed point when it passes its final check; otherwise
          the pre-pass runs as without the switch. The point is an atom set
          already known to be a solution when it is one at all -- the graph
          [PCSP.RecFunGraph] records for each unknown it introduces -- which,
          diluted among the generated atoms, waits behind every question about
          them. Contract: the first run returns only a fixed point that passed
          the ordinary final check, so a [sat] from it is sound exactly as the
          pre-pass's is; when it does not answer, the second run is the pre-pass
          of this configuration as it would have been, with its own budget.
          [false]: one run, generated and declared atoms together *)
  candidates : candidates;
      [@default Common.Util.config_default candidates_of_yojson "{}"]
  quotas : quotas; [@default Common.Util.config_default quotas_of_yojson "{}"]
  questions : questions;
      [@default Common.Util.config_default questions_of_yojson "{}"]
  final_check : final_check;
      [@default Common.Util.config_default final_check_of_yojson "{}"]
}
[@@deriving yojson]

(** The value each of the pre-pass's former flat switches takes under a
    configuration. A variant above folds a switch and the parameters read only
    under it into one choice; the pre-pass reads booleans and options, and these
    functions unfold the choice. Contract: under every choice each function
    returns the value the code reads, and where the choice makes a parameter
    inert (its mechanism is off) it returns that parameter's default, which no
    reader looks at: its readers are reached only under the constructor that
    carries it. *)
module Switch = struct
  (* the pre-pass runs before the first synthesis, eagerly, lazily or in a
     forked copy *)
  let before_synthesis h =
    match h.schedule with
    | Before_synthesis _ | Parallel _ -> true
    | Off | In_first_validation -> false

  (* the pre-pass runs inside the first validation (when it has not run
     before); never under [Parallel] *)
  let declared_atoms h =
    match h.schedule with
    | In_first_validation -> true
    | Before_synthesis { in_first_validation; _ } -> in_first_validation
    | Off | Parallel _ -> false

  (* the old switch, read only with [before_synthesis]: its default [true]
     where the schedule does not run the pre-pass before synthesis *)
  let in_parallel h =
    match h.schedule with
    | Parallel _ -> true
    | Before_synthesis _ -> false
    | Off | In_first_validation -> true

  let after_ms h =
    match h.schedule with
    | Before_synthesis { after_ms; _ } -> after_ms
    | _ -> None

  (* the copy's budget: [None] with [parallel_unbounded] *)
  let parallel_unbounded h =
    match h.schedule with
    | Parallel { budget = Unbounded } -> true
    | Parallel { budget = Bounded _ } -> false
    | Off | In_first_validation | Before_synthesis _ -> true

  let parallel_budget_ms h =
    match h.schedule with
    | Parallel { budget = Bounded { budget_ms } } -> budget_ms
    | _ -> None

  let drop_by_model h =
    match h.questions.drop_by_model with
    | Drop_by_model _ -> true
    | No_drop_by_model -> false

  let drop_by_model_solver_ms h =
    match h.questions.drop_by_model with
    | Drop_by_model r -> r.solver_ms
    | No_drop_by_model -> None

  let drop_by_model_quantified_aside h =
    match h.questions.drop_by_model with
    | Drop_by_model r -> r.quantified_aside
    | No_drop_by_model -> false

  let drop_by_model_batch_ms h =
    match h.questions.drop_by_model with
    | Drop_by_model r -> r.batch_ms
    | No_drop_by_model -> None

  let drop_by_model_conjunction_ms h =
    match h.questions.drop_by_model with
    | Drop_by_model r -> r.conjunction_ms
    | No_drop_by_model -> Some 6000

  let conjunction_plain_first_ms h =
    match h.questions.drop_by_model with
    | Drop_by_model r -> r.conjunction_plain_first_ms
    | No_drop_by_model -> None

  let inclusions_second_round h =
    match h.candidates.inclusions.second_round with
    | Second_round _ -> true
    | No_second_round -> false

  let inclusion_round_budget_ms h =
    match h.candidates.inclusions.second_round with
    | Second_round { budget_ms } -> budget_ms
    | No_second_round -> None

  (* the constructors from the former flat values (the legacy translation's
     mapping, for a caller that states the switches one by one): each gives
     the choice the old fields denote, dropping the values the old code did
     not read under the others *)
  let schedule_of ~before_synthesis ~in_parallel ~declared_atoms ~after_ms
      ~parallel_unbounded ~parallel_budget_ms =
    if not before_synthesis then
      if declared_atoms then In_first_validation else Off
    else if in_parallel then
      Parallel
        {
          budget =
            (if parallel_unbounded then Unbounded
             else Bounded { budget_ms = parallel_budget_ms });
        }
    else Before_synthesis { after_ms; in_first_validation = declared_atoms }

  let drop_by_model_of ~on ~solver_ms ~quantified_aside ~batch_ms
      ~conjunction_ms ~conjunction_plain_first_ms =
    if on then
      Drop_by_model
        {
          solver_ms;
          quantified_aside;
          batch_ms;
          conjunction_ms;
          conjunction_plain_first_ms;
        }
    else No_drop_by_model

  let second_round_of ~on ~budget_ms =
    if on then Second_round { budget_ms } else No_second_round
end
