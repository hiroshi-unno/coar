(* No configuration instantiates this module.  The resolver variant [Graph]
   builds [GraphResolver], and takes its payload from the [Config] below, because [GraphResolver.Make] has
   no [Config] of its own and is a functor over [SMTResolver.Config.ConfigType].
   So this file's [Config] is live and the rest of it is not run.

   It is kept on purpose: an SMT-based resolver may be written here again.  What
   that costs meanwhile is that the code below has not been maintained against
   the rest -- [contradicts] and [acquire_papp] still derive an example from a
   model without the guard that a term whose value the theory leaves open
   needs -- so anything revived from it has to be
   read against [GraphResolver] first, not merely compiled. *)

open Core
open Common
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld
open PCSatCommon

module Config = struct
  type t = {
    verbose : bool; [@default false]
    only_diff : bool; [@default true]  (** use only newly added positive/negative examples *)
    refute : bool; [@default true]  (** try to refute existing positive/negative examples *)
    decide : bool; [@default true]  (** try to decide undecided atoms *)
    acquire_und : bool; [@default true]
        (** try to acquire new positive/negative examples from undecided
            examples *)
    resolve_against_problem_clauses : bool; [@default true]
        (** Resolve the decided examples one step against the PROBLEM's own
            clauses (and the learned ones) and keep the resolvents as new
            examples.  The refutation step already resolves a decided atom
            against those clauses, but only to ask whether the result
            contradicts what is decided, and a resolvent that does not is
            dropped; this keeps it, so a derivation that needs an
            intermediate fact -- a positive [P(a, 0)] for every [a], pushed
            through a loop clause to [P(a, 1)] for every [a], which a goal
            clause then refutes -- completes across rounds instead of waiting
            for the validator to return a matching point.  It costs a larger
            example set, which makes a synthesis heavier. *)
    problem_clause_sources_parametric_only : bool; [@default false]
        (** Resolve against the problem's clauses only from decided examples
            that are themselves PARAMETRIC.  The refutation this site was
            measured to supply comes from a parametric positive instantiated at
            the standard dummy -- a constant array, which met a goal clause --
            while a ground example yields resolvents that only add points, and
            those are what the site costs.  A different cut from the next
            field, which filters by what a resolvent turns into and so drops
            the very point that refutes.  Unmeasured. *)
    problem_clause_resolvents_parametric_only : bool; [@default false]
        (** Of the examples the problem-clause site above adds, keep only the
            PARAMETRIC ones -- regions, statements for every value of some
            parameter -- and drop the ground points.  The derivation that site
            exists for is a region pushed through a clause to a region; the
            points it also produces are what makes the example set, and so the
            synthesis, heavier.  Measured, and the premise is wrong: the
            refutation this site supplies on the input it was built for is a
            ground conflict at the parametric example's dummy instance, which
            this filter drops, so that input is lost while the cost on the
            ordinary lists stays.  Kept off; the source filter above is the cut
            that follows the actual derivation. *)
    problem_clause_self_loops_parametric_only : bool; [@default false]
        (** At the problem-clause site above, resolve through a SELF-LOOP
            clause -- one whose head predicate also occurs in its body, a loop
            step [P(x) /\ c -> P(x')] -- only from PARAMETRIC decided examples.
            A ground example pushed through such a clause yields one more
            ground point of the same predicate, which the next round pushes
            again: the loop is unrolled one step per round, every point new,
            and the example set (and the labeling's pairwise conflict test over
            it) grows without the region a refutation needs.  A parametric
            source through the same clause is a region pushed to a region,
            which is the derivation the site exists for, and every other clause
            still takes every decided source.  It does not stop the unrolling
            itself: a parametric example pushed through the loop is again
            parametric and is pushed again the next round, and on the counter
            loop that motivated it half of what the site added was such
            parametric chains; the depth bound below is the cut for that. *)
    problem_clause_self_loop_depth_bound : bool; [@default true]
        (** At the problem-clause site above, bound how many times one chain is
            pushed through a SELF-LOOP clause: an example derived through such a
            clause from an example of depth [d] has depth [d + 1], an example
            obtained any other way has depth 0, and only examples of depth
            below [problem_clause_self_loop_depth] are resolved through a
            self-loop, one step per chain per round.  Without it a loop whose
            step is total in the direction of the push is unrolled one step per
            round from every example the validator ever returned, parametric
            and ground alike, so the examples added per round grow with the
            round number: on a counter loop the negatives reached 260 by the
            sixteenth round against 24 at the answer without the site, the
            positives 31 against 6, and most of the time went to the labeling's
            pairwise conflict test over them.  Non-loop clauses are not
            bounded: a chain through them ends when the predicates do, except
            around a cycle of two or more clauses, which this bound does not
            see.  An example derived through a non-loop clause has depth 0. *)
    problem_clause_self_loop_depth : int; [@default 2]
        (** the bound of the field above; read only when it is on.  A
           refutation that needs a region pushed through a loop several times
           is reached through the site only up to this many steps per chain:
           on a range loop of five iterations a bound of 1 lost the refutation
           that bounds 2 and 3 kept, in one run each.  The default 2 answered
           the counter loop that motivated the bound in every run of a family
           of five collector settings where 3 missed one, and over a group of
           232 CHC and Thrust inputs it gained three answers the unbounded site
           had lost and lost one. *)
    problem_clause_self_loop_depth_arrays : int option; [@default Some 10]
        (** with [Some n], the bound of the two fields above for a source
            example whose predicate can reach an array -- an argument sort that
            is an array or holds one in a tuple or datatype field, to three
            datatype levels -- is [n]; every other source keeps
            [problem_clause_self_loop_depth].  [None] is that bound for every
            source, the same examples in the same order.  The default is
            [Some 10].  It
            exists because a bound of 10 everywhere gained three stable answers
            on array inputs and lost one on an input without arrays, where a
            region pushed further through an integer loop only grew the example
            set; reachability rather than the top-level sort decides, since a
            predicate derived from a Rust program takes its arrays inside the
            tuple its arguments arrive in. *)
    problem_clause_self_loop_depth_arrays_program_only : bool; [@default false]
        (** with [problem_clause_self_loop_depth_arrays] set, give its bound only
            to a source example whose predicate reaches an array through a
            position that is not a universal relation: a [Bool]-valued array
            argument that every clause applying the predicate passes on as one
            and the same variable.  That is the shape a dependency set gives --
            a universally quantified relation the witness may see, such as a
            trait invariant over a quantified sort, is an array-sorted free
            variable of each clause handed to the predicate unchanged -- and it
            is a parameter of the contract, not state the loop changes, so
            pushing a region further through the loop only grows the example
            set as on an input without arrays.  Measured on a generic
            Rust-derived loop over such a relation: the larger bound recorded
            411 examples by the answer against 71 for the same program with the
            relation instantiated, and the labeling and resolution phases took
            five to eight times as long per round.  A predicate that also
            reaches an array of the program keeps the larger bound.  It changes
            which examples are derived and nothing else, so it cannot bear on
            the soundness of a verdict. *)
    eager_positive_examples : bool; [@default false]
        (** derive positive examples forwards from the clauses, in addition to
            the resolution rules below.  Where those decide an atom by
            contradiction, one literal at a time, this applies a clause in the
            forward direction with ALL of its body atoms matched against
            examples already decided positive, and takes its head.  A clause
            with no body atoms and a false pure part is the degenerate case and
            yields its head unconditionally.

            Off by default and unmeasured: the rule is sound but its yield
            against the resolution rules' own is not known, and deriving
            examples nothing goes on to use is a cost without a benefit. *)
    eager_one_query : bool; [@default false]
        (** which of the two searches the forward rule uses for the matching:
            one solver query with a disjunction over the candidate matches, or
            the default, one query per pairing.  They are the same rule and
            running both derives every example twice. *)
    eager_smt_timeout : int option; [@default None]
        (** budget for the matching queries of the field above *)
    resolution_query_timeout : int option; [@default Some 10000]
        (** budget in milliseconds for the solver questions of the two
            resolution rules (the contradiction test and the derivation of a
            positive example).  An undecided question derives nothing, so a
            budget can lose an answer and cannot make one wrong.  Chosen far
            above what these questions take when they are decided: over 81
            constrained Horn and Thrust inputs, 4077 such questions, every one
            decided and the slowest in 73 ms.  Independently of it, the contradiction
            test does not ask a question quantified over a sequence at all,
            since a budget is not known to bound one. *)
    solve_store_chain_eqs : bool; [@default true]
        (** before a resolution question is asked, replace each top-level
            conjunct [store (.. store (x, c1, v1) ..) cn vn = A] (integer
            literal indices, [x] an array variable occurring neither in [A] nor
            in a written value) by the equisatisfiable
            [x = store (.. (A, c, y_c) ..) /\ select A c = w_c] with fresh
            [y_c] ([Ast.StoreChainEq]): an array equation whose other side is a
            [lambda] leaves Z3 with a quantifier it does not decide within any
            budget, while the rewritten form defines [x] and is decided at
            once.  The fresh variables are removed from a returned model. *)
    solve_store_chain_eqs_contextual : bool; [@default false]
        (** with [solve_store_chain_eqs], also rewrite a write-chain equation
            that sits under an [ite] whose condition the question's own linear
            literals decide ([Ast.StoreChainEq.solve_contextual]): the [ite]
            is replaced by its branch, an exact rewrite, before the equation is
            solved.  A step clause that writes [ite (v = i) (store a i 0)
            (store a i i)] gives questions of that shape, which otherwise reach
            Z3 as a lambda extensionality question it leaves undecided at any
            budget. *)
    decide_by_fact_goal_clauses : bool; [@default true]
        (** decide the polarity of atoms the loop already holds from the
            problem's own fact and goal clauses instantiated at their
            arguments: an atom of an undecided example, or of a decided one of
            the opposite polarity, becomes a positive where a fact clause has
            an instance asserting it and a negative where a goal clause does.
            The resolution rules below start from DECIDED examples, so a point
            no decided example resolves onto is out of their reach however many
            rounds run; this starts from the clause.  The rule is the HoIce
            tool paper's post-extraction simplification with its satisfiability
            test replaced where it would be unsound here; the argument is at
            the head of [FactGoal].  On by default, and by default gated by
            [fact_goal_structured_only] below. *)
    fact_goal_structured_only : bool; [@default true]
        (** a firing condition for [decide_by_fact_goal_clauses]: run it only
            on a problem that declares a forall-sort or whose unknowns'
            parameters or clauses' variables have a datatype, sequence or
            array sort ([FactGoal.structured_problem]).  On a problem over
            integers and reals alone the pass asks questions that decide
            nothing the loop lacks and still move the trajectory, since asking
            goes to the pooled solver context and allocates; not asking is the
            only way to remove that.  On by default. *)
    decide_by_witness_groups : bool; [@default false]
        (** decide a head atom the loop holds (or refute the problem) through
            the totality of functional witnesses: for a group of clauses that
            share their head and their functional body atoms, whose results
            are variables, the head at [v] is a positive when [exists x.
            head(x) = v /\ forall y. \/_m (Phi_m /\ U(B_m))] is valid, [U]
            reading each other body atom through the decided positives
            ([FactGoal.witness_query], where the argument is).  A clause body
            universal skolemised into a witness is otherwise split by the
            clausal form over clauses that each fix the witness's value, and
            the labeling escapes the head one value at a time.  Same budget,
            cache and per-round cap as the pass above, independent of its
            gates.  [false]: no such question *)
    fact_goal_dry_run : bool; [@default false]
        (** a control for the field above, not a feature: ask every question
            it would ask, with the same budget, cache and cap, and then record
            nothing, so that a run differs from one with the pass off only by
            the questions having been put to the solver.  Asking perturbs the
            trajectory by itself (the questions go to the pooled solver
            context and allocate), and a comparison of the pass on against off
            on a single file cannot tell that effect from the examples' own
            without this arm.  Nothing is derived, so it cannot change a
            verdict's soundness in either direction. *)
    unify_parameters : bool; [@default true]
        (** realise as BINDINGS the matching equations that have a parameter on
            one side, instead of handing all of them to a solver for one
            arbitrary solution.  This is what lets one example's parameter meet
            another's; two distinct parameters no more meet than two distinct
            constants do, so introducing parameters without binding them changes
            what two examples disagree about and not whether they do.

            Independent of the flag below, which is the half measured to cost
            answers.  This one is measured at 0 verdict disagreements and 0
            answers lost over 168 benchmarks, which is why it is on; the
            bindings merge into the model's substitution keeping the MODEL's
            value where the two disagree, because that is the one the rest of
            the derivation was built against -- dropping it for a binding raised
            an exception that ended the run. *)
    generalise_matching : bool; [@default false]
    generalise_invented_values : bool; [@default false]
        (** the selective form of the field above, and the one the measurement
            asks for.  [generalise_matching] opens EVERY variable of the
            matching condition; this opens only the numeric leaves of the
            model's values that the problem does not state, leaving the
            program's own constants where they are.

            Why the distinction is not cosmetic: the derived example is the
            matching condition with the substitution applied, so whatever is
            opened stays constrained by that condition and the model's own value
            witnesses it -- the same argument at either setting. What differs is
            what the example SAYS. Opening everything asserts the property for
            every instantiation of the condition, which is a much stronger claim
            and is measured to cost a satisfiable twin its answer; opening the
            values a solver merely picked asserts only that the arbitrary choice
            was arbitrary.

            Why it is wanted here: with the validator's side generalised, two
            runs of one binary that are byte-identical for 1,235 lines of trace
            then differ in this substitution -- `#tvar1113 |-> 11` against
            `|-> 8`, neither value in the problem -- which is the first place
            address-space randomization becomes visible once the validator stops
            recording invented numbers. The values are mixed: some are numbers
            and some are structured terms holding numbers, so the rewriting goes
            into the term as it does on the validator's side. *)
    record_goal_reads : bool; [@default true]
        (** when a negative example is derived by refuting an atom against a
            clause, record in the side table [GoalReads] the indices at which
            that clause reads the atom's arrays, evaluated at the derivation's
            substitution -- the resolver's half of the validator switch of the
            same name.  From a goal clause the record is exact (it is all the
            refutation reads); from a clause with a head it is offered beside
            the default cells, since the head's own witness is not among the
            reads.  The derived example itself is unchanged.  Off by
            default. *)
    inherit_goal_reads : bool; [@default false]
        (** when a negative example is derived by resolving a clause's head
            (a problem clause's, or a step example's the validator returned)
            against a decided negative example of the same predicate, give the
            derived atom the records [GoalReads] holds for that negative
            example, each joined with the resolved clause's own reads at the
            derivation's instance and keeping its exactness
            ([GoalReads.inherit_records]).  The witness index of the later
            goal is then among the derived atom's cells, where otherwise an
            atom whose default product is over the bound gets one sampled
            tuple.  Where something was inherited, the plain record of
            [record_goal_reads] is not filed beside it, since a record offered
            beside the default cells makes the whole expansion fall back.
            Any set of cells is sound, so this changes which constraint
            stands for the example, never what the example says.  Off by
            default. *)
    vary_derived_array_defaults : bool; [@default false]
        (** when resolution against a clause derives a POSITIVE example from a
            model of the matching condition, give each array of the model that
            the condition reads only through [select] a default of its own --
            distinct per array and from every integer of the model, the
            condition and the atom -- keeping the model's value at every
            position the condition reads, and keep the new model only if the
            condition still evaluates to [true] on it (the contract is at the
            head of [VaryArrays]).  The solver's cheapest model gives every
            such array the same constant, and an example over equal constant
            arrays is fitted by a candidate relating the arrays by value alone,
            so the loop sees no positive forcing an index relation between
            them.  Soundness is resolution's own licence: any model of the
            condition licenses the example, and the evaluation decides that
            the new one is a model.  Off by default. *)
    keep_example_params : bool; [@default false]
        (** do not substitute into a position the incoming example left open:
            move the equation into the guard, so two examples derived at
            different values remain the same atom *)
    collapse_same_pred : bool; [@default false]
        (** before dropping a resolvent that is not a unit clause, try to
            collapse several applications of one predicate into one, guarded by
            the condition under which their arguments agree *)
        (** when resolution matches two examples it solves the matching
            condition for a model and writes the model's values into the derived
            example.  A solver assigns a value to everything the query
            constrains, forced or not, so the example is more concrete than the
            derivation was: two examples meaning the same thing become different
            atoms and never collide, which is why a refutation whose chain the
            loop does unroll is still not found.  With this on the open
            variables become parameters and the condition travels as the
            example's side condition, which is what the resolution concluded. *)
    unit_prop : bool; [@default false]  (** perform unit propagation, on every round *)
    simplify_with_matching : bool; [@default false]
        (** let a decided example settle a clause literal it equals only up to a
            substitution. The simplification is a set difference today, so a
            head a decided negative has already refuted survives whenever the
            two differ by a renaming of their parameters, and the clause stays
            undecided for the rest of the run. The test asked is validity, not
            satisfiability: the literal is removed unconditionally, so the
            example has to settle it at every value of the clause's parameters *)
    keep_model_over_matcher : bool; [@default false]
        (** when the model a resolution step found disagrees with the step's own
            matcher, keep the model's value and let the later compatibility
            check decide, instead of discarding the whole step. The two sites
            that build an example from a model already differ here: one keeps
            the model's value because the rest of the derivation was built
            against it, the other requires the two to be syntactically equal and
            raises otherwise, which is strictly stronger than the compatibility
            test applied afterwards and fires first *)
    unit_prop_when_stalled : bool; [@default false]
        (** perform unit propagation only on the rounds where the synthesis
            phase has reported that it cannot fit the examples.  Unit
            propagation raises what each resolution round derives, which is what
            a refutation needs and what an invariant search is slowed by --
            measured over one corpus, switching it on unconditionally gains one
            answer and loses one, and they are the two sides of one program.
            Doing it only where the loop is stuck takes the first without the
            second, since a run whose synthesis keeps succeeding never sets the
            flag. *)
    enforce_new : bool; [@default false]
    parametric_examples : bool; [@default true]
    add_unit_clause_as_is : bool; [@default false]
  }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let instantiate_ext_files cfg = Ok cfg
end

module Make
    (Config : Config.ConfigType)
    (APCSP : PCSP.Problem.ProblemType) : sig
  val run_phase : int -> State.u -> State.u Or_error.t
end = struct
  let config = Config.config
  let id = PCSP.Problem.id_of APCSP.problem

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id
  let old_dpos = ref Set.Poly.empty
  let old_dneg = ref Set.Poly.empty
  let old_und = ref Set.Poly.empty

  exception E

  let unifiable =
    let open Atom in
    function
    | True _, True _ | False _, False _ -> Some (Formula.mk_true ())
    | App (pred, terms, _), App (pred', terms', _)
      when Stdlib.( = ) pred pred' && List.length terms = List.length terms'
      -> (
        try
          Some
            (Formula.and_of
            @@ List.filter_map (List.zip_exn terms terms') ~f:(function
              | FunApp (T_int.Int n1, [], _), FunApp (T_int.Int n2, [], _) ->
                  if Z.Compare.( = ) n1 n2 then None else raise E
              | FunApp (T_real.Real r1, [], _), FunApp (T_real.Real r2, [], _)
                ->
                  if Q.( = ) r1 r2 then None else raise E
              | ( FunApp (T_bool.Formula (Formula.Atom (atm1, _)), [], _),
                  FunApp (T_bool.Formula (Formula.Atom (atm2, _)), [], _) )
                when (Atom.is_true atm1 || Atom.is_false atm1)
                     && (Atom.is_true atm2 || Atom.is_false atm2) ->
                  if
                    (Atom.is_true atm1 && Atom.is_true atm2)
                    || (Atom.is_false atm1 && Atom.is_false atm2)
                  then None
                  else raise E
              | t1, t2 -> Some (Formula.eq t1 t2)))
        with E -> None)
    | _ -> None

  let contradicts ~dpos ~dneg fenv exi_senv
      ((uni_senv, c_pos, c_neg, c_phi), params, theta) =
    try
      (*Debug.print @@ lazy ("  checking contradiction: " ^ Clause.str_of exi_senv (uni_senv, c_pos, c_neg, c_phi));*)
      let positive = Set.Poly.filter_map ~f:ExClause.old_atom_of_uclause dpos in
      let negative = Set.Poly.filter_map ~f:ExClause.old_atom_of_uclause dneg in
      let eqs =
        Set.union
          (Set.Poly.map c_pos ~f:(fun atm ->
               let xs =
                 Set.Poly.filter_map negative ~f:(fun neg_atm ->
                     let _param_senv (*ToDo*), atm' =
                       Atom.refresh_tvar neg_atm
                     in
                     unifiable
                       (Logic.ExtTerm.to_old_atm exi_senv uni_senv atm, atm'))
                 |> Set.to_list
               in
               if List.is_empty xs then raise E else Formula.or_of xs))
          (Set.Poly.map c_neg ~f:(fun atm ->
               let xs =
                 Set.Poly.filter_map positive ~f:(fun pos_atm ->
                     let _param_senv (*ToDo*), atm' =
                       Atom.refresh_tvar pos_atm
                     in
                     unifiable
                       (Logic.ExtTerm.to_old_atm exi_senv uni_senv atm, atm'))
                 |> Set.to_list
               in
               if List.is_empty xs then raise E else Formula.or_of xs))
        |> Set.to_list
      in
      let phi =
        Formula.and_of
        @@ Formula.mk_neg (Logic.ExtTerm.to_old_fml exi_senv uni_senv c_phi)
           :: eqs
      in
      let fvs = Formula.term_sort_env_of phi in
      let bvs = Set.filter fvs ~f:(fst >> Map.Poly.mem exi_senv >> not) in
      let cond =
        Formula.exists (Set.to_list bvs)
          phi (* unbound variables are non-predicate function variables *)
      in
      (*Debug.print @@ lazy ("    sufficient condition: " ^ Formula.str_of cond ^ " is valid?");*)
      if Set.eqlen fvs bvs then
        (* without non-predicate function variables*)
        match Z3Smt.Z3interface.check_sat ~id fenv [ phi ] with
        | `Sat model ->
            (*Debug.print @@ lazy "    yes";*)
            let sub =
              (* the same rule as the sibling resolver, and it has to be here
                 too: a pooled solver's model describes every symbol its context
                 knows, including declarations left by earlier queries, and this
                 substitution is keyed by NAME and applied to the clause's own
                 atom.  A left-over entry then replaces a variable by a value of
                 the wrong sort -- a list where an element belongs -- and the
                 next query that term reaches is rejected outright.  Fixing only
                 the sibling left this one producing them, and a benchmark went
                 on crashing in three runs of three. *)
              LogicOld.model_subst ~freshvar:true model
                ~target:
                  (Set.union fvs
                     (Set.Poly.map ~f:(fun (x, so) ->
                          (x, Logic.ExtTerm.to_old_sort so))
                     @@ Map.to_set uni_senv))
            in
            let theta = Map.Poly.map theta ~f:(Term.subst sub) in
            Some
              (Map.Poly.merge sub theta ~f:(fun ~key:_x -> function
                | `Left v | `Right v -> Some v
                | `Both (v1, v2) ->
                    if Stdlib.(v1 = v2) then Some v1
                    else
                      (*failwith (Ident.name_of_tvar x ^ ":" ^ LogicOld.Term.str_of v1 ^ ":" ^ LogicOld.Term.str_of v2)*)
                      raise E))
        | _ -> (*Debug.print @@ lazy "    no";*) None
      else if Set.are_disjoint (Set.Poly.map ~f:fst bvs) params then
        (* with function variables and without parameters *)
        if Evaluator.is_valid (Z3Smt.Z3interface.is_valid ~id fenv) cond then
          (*let _ = Debug.print @@ lazy "    yes" in*) Some theta
        else (*let _ = Debug.print @@ lazy "    no" in*) None
      else None
    with E ->
      (*Debug.print @@ lazy "    unification failed";*)
      None

  let contradicts_assuming_pos ~dpos ~dneg fenv exi_senv cs (param_senv, atm) =
    let params =
      Set.filter ~f:(Fn.non @@ Map.Poly.mem exi_senv) @@ Atom.fvs_of atm
    in
    ClauseSet.resolve_one_step_all ~print:Debug.print
      (Set.Poly.singleton
         (Logic.of_old_sort_env_map param_senv, Logic.ExtTerm.of_old_atom atm))
      Set.Poly.empty exi_senv cs
    |> Set.find_map ~f:(fun (c, sub) ->
        contradicts ~dpos ~dneg fenv exi_senv
          (c, params, Map.Poly.filter_keys sub ~f:(Set.mem params)))

  let contradicts_assuming_neg ~dpos ~dneg fenv exi_senv cs (param_senv, atm) =
    let params =
      Set.filter ~f:(Fn.non @@ Map.Poly.mem exi_senv) @@ Atom.fvs_of atm
    in
    ClauseSet.resolve_one_step_all ~print:Debug.print Set.Poly.empty
      (Set.Poly.singleton
         ( Map.Poly.map param_senv ~f:Logic.ExtTerm.of_old_sort,
           Logic.ExtTerm.of_old_atom atm ))
      exi_senv cs
    |> Set.find_map ~f:(fun (c, sub) ->
        contradicts ~dpos ~dneg fenv exi_senv
          (c, params, Map.Poly.filter_keys sub ~f:(Set.mem params)))

  let acquire_papp fenv parametric ucs pure atm =
    let x, _, ts, _ = Atom.let_pvar_app atm in
    Debug.print @@ lazy ("checking " ^ Atom.str_of ~priority:0 atm);
    let enforce_new =
      if config.enforce_new then
        Formula.and_of @@ Set.to_list
        @@ Set.Poly.map (Set.Poly.filter_map ucs ~f:ExClause.papp_of_uclause)
             ~f:(fun ((y, _), ts') ->
               if Stdlib.(x = y) then
                 Formula.or_of
                   (List.map2_exn ts ts' ~f:(fun t t' ->
                        (*ToDo: here t' is assumed to have no variable*)
                        assert (Set.is_empty @@ Term.tvs_of t');
                        Formula.neq t t'))
               else Formula.mk_true ())
      else Formula.mk_true ()
    in
    match
      Z3Smt.Z3interface.check_sat ~id fenv [ Formula.mk_neg pure; enforce_new ]
    with
    | `Sat model ->
        Some
          (LogicOld.model_subst ~freshvar:parametric model
             ~target:
               (Set.union
                  (Formula.term_sort_env_of
                  @@ Formula.and_of [ Formula.mk_neg pure; enforce_new ])
                  (Atom.term_sort_env_of atm)))
    | _ -> None

  let acquire fenv exi_senv ~dpos ~dneg ~und cs =
    if Set.is_empty cs then (dpos, dneg, und)
    else (
      Debug.print @@ lazy "********** one-step resolved constraints ***********";
      Debug.print
      @@ lazy
           (PCSP.Problem.str_of
              (PCSP.Problem.of_clauses ~params:(PCSP.Params.make exi_senv) cs));
      Debug.print @@ lazy "";
      let unknowns = Map.key_set exi_senv in
      Set.fold cs ~init:(dpos, dneg, und)
        ~f:(fun (dpos, dneg, und) (uni_senv, pos, neg, pure) ->
          match (Set.to_list pos, Set.to_list neg) with
          | [ atm ], [] | [], [ atm ] ->
              let atm = Logic.ExtTerm.to_old_atm exi_senv uni_senv atm in
              let pure = Logic.ExtTerm.to_old_fml exi_senv uni_senv pure in
              let tvs = Set.union (Atom.tvs_of atm) (Formula.tvs_of pure) in
              let fnvs = Set.inter tvs (Map.key_set exi_senv) in
              (* if Set.exists (Set.Poly.union_list [Formula.pvs_of pure;Atom.pvs_of atm] |> Set.Poly.map ~f:Ident.pvar_to_tvar) ~f:(PCSP.Problem.is_tot_pred APCSP.problem) || true then
                 dpos, dneg, und
                 else *)
              if Set.is_empty fnvs then (
                (* without function variables *)
                let parametric =
                  config.parametric_examples && Fn.non Set.is_empty tvs
                in
                if Set.is_empty neg then (
                  if
                    (* positive unit clause *)
                    parametric && config.add_unit_clause_as_is
                  then assert false
                  else
                    match acquire_papp fenv parametric dpos pure atm with
                    | None -> (dpos, dneg, und)
                    | Some sub ->
                        Debug.print
                        @@ lazy
                             ("  added as a positive example with: "
                             ^ LogicOld.TermSubst.str_of sub);
                        let cl =
                          ExClause.normalize_params unknowns
                          @@ ExClause.mk_unit_pos
                          @@ ExAtom.of_old_atom exi_senv (Formula.mk_true ())
                          @@ Atom.subst sub atm
                        in
                        (Set.add dpos cl, dneg, und))
                else if
                  (* negative unit clause *)
                  parametric && config.add_unit_clause_as_is
                then assert false
                else
                  match acquire_papp fenv parametric dneg pure atm with
                  | None -> (dpos, dneg, und)
                  | Some sub ->
                      Debug.print
                      @@ lazy
                           ("  added as a negative example with: "
                           ^ LogicOld.TermSubst.str_of sub);
                      let cl =
                        ExClause.normalize_params unknowns
                        @@ ExClause.mk_unit_neg
                        @@ ExAtom.of_old_atom exi_senv (Formula.mk_true ())
                        @@ Atom.subst sub atm
                      in
                      (dpos, Set.add dneg cl, und))
              else (* with function variables *) (dpos, dneg, und)
          | [], [] -> (
              let pure = Logic.ExtTerm.to_old_fml exi_senv uni_senv pure in
              let tvs = Formula.tvs_of pure in
              let fnvs = Set.inter tvs (Map.key_set exi_senv) in
              if Set.is_empty fnvs then
                (* without function variables *)
                (dpos, dneg, und)
              else
                (* with function variables *)
                match
                  ExClause.make exi_senv Set.Poly.empty Set.Poly.empty pure
                with
                | None -> (dpos, dneg, und)
                | Some cl ->
                    ( dpos,
                      dneg,
                      (*ToDo*)
                      Set.add und (ExClause.normalize_params unknowns cl) ))
          | _, _ -> (dpos, dneg, und)))

  let prove ~dpos ~dneg fenv exi_senv cs (param_senv, atm) =
    match
      contradicts_assuming_neg ~dpos ~dneg fenv exi_senv cs (param_senv, atm)
    with
    | Some sub ->
        Debug.print
        @@ lazy
             ("  added as a positive example with: "
             ^ LogicOld.TermSubst.str_of sub);
        let unknowns = Map.key_set exi_senv in
        let cl =
          ExClause.normalize_params unknowns
          @@ ExClause.mk_unit_pos
          @@ ExAtom.of_old_atom exi_senv (Formula.mk_true ())
          @@ Atom.subst sub atm
        in
        Debug.print @@ lazy ("  add positive example " ^ ExClause.str_of cl);
        Set.add dpos cl
    | None -> dpos

  let refute ~dpos ~dneg fenv exi_senv cs (param_senv, atm) =
    match
      contradicts_assuming_pos ~dpos ~dneg fenv exi_senv cs (param_senv, atm)
    with
    | Some sub ->
        Debug.print
        @@ lazy
             ("  added as a negative example with: "
             ^ LogicOld.TermSubst.str_of sub);
        let unknowns = Map.key_set exi_senv in
        let cl =
          ExClause.normalize_params unknowns
          @@ ExClause.mk_unit_neg
          @@ ExAtom.of_old_atom exi_senv (Formula.mk_true ())
          @@ Atom.subst sub atm
        in
        Debug.print @@ lazy ("  add negative example " ^ ExClause.str_of cl);
        Set.add dneg cl
    | None -> dneg

  let resolve e =
    let open State.Monad_infix in
    Ok e >>=? fun vs _a ->
    let dpos0, dneg0, und0 = VersionSpace.pos_neg_und_examples_of vs in
    let d_dpos = Set.diff dpos0 !old_dpos in
    let d_dneg = Set.diff dneg0 !old_dneg in
    let d_und = Set.diff und0 !old_und in
    let fenv = vs.fenv in
    old_dpos := dpos0;
    old_dneg := dneg0;
    old_und := und0;
    (* Debug.print @@ lazy "********** examples ***********";
       Debug.print @@ lazy (ExClauseSet.str_of dpos0);
       Debug.print @@ lazy (ExClauseSet.str_of dneg0);
       Debug.print @@ lazy (ExClauseSet.str_of und0); *)
    let cs = PCSP.Problem.clauses_of APCSP.problem in
    let exi_senv = PCSP.Problem.senv_of APCSP.problem in
    let dpos, dneg =
      let to_be_refuted, to_be_proved =
        let to_be_refuted, to_be_proved =
          if config.refute then
            ( Set.Poly.filter_map
                (if config.only_diff then d_dpos else dpos0)
                ~f:(fun c -> ExAtom.to_old_atom @@ ExClause.exatom_of_uclause c),
              Set.Poly.filter_map
                (if config.only_diff then d_dneg else dneg0)
                ~f:(fun c -> ExAtom.to_old_atom @@ ExClause.exatom_of_uclause c)
            )
          else (Set.Poly.empty, Set.Poly.empty)
        in
        if config.decide then
          let atms =
            Set.Poly.filter_map ~f:ExAtom.to_old_atom
            @@ Set.concat_map ~f:ExClause.exatoms_of
            @@
            (* Set.filter ~f:(fun ex ->
                Debug.print @@ lazy ("decide:" ^ ExClause.str_of ex);
                let pvs = ExClause.pvs_of ex |> Set.Poly.map ~f:Ident.pvar_to_tvar in
                not @@ Set.exists pvs ~f:(PCSP.Problem.is_tot_pred APCSP.problem)) @@ *)
            if config.only_diff then d_und else und0
          in
          (Set.union to_be_refuted atms, Set.union to_be_proved atms)
        else (to_be_refuted, to_be_proved)
      in
      let bvs = Map.key_set exi_senv in
      Set.union
        (Set.Poly.map ~f:(fun a -> (false, a))
        @@ ExAtomSet.reduce bvs to_be_refuted)
        (Set.Poly.map ~f:(fun a -> (true, a))
        @@ ExAtomSet.reduce bvs to_be_proved)
      |> Set.Poly.map ~f:(fun (b, (param_senv, atm)) ->
          (Map.Poly.length param_senv, b, (param_senv, atm)))
      |> Set.to_list
      |> List.sort ~compare:(fun (n1, _, _) (n2, _, _) -> n2 - n1)
      |> List.fold ~init:(dpos0, dneg0)
           ~f:(fun (dpos, dneg) (_, b, (param_senv, atm)) ->
             if b then (
               Debug.print
               @@ lazy
                    ("proving "
                    ^ Formula.str_of
                        ((*Formula.exists (Set.to_list @@ Atom.term_sort_env_of atm) @@*)
                         Formula.mk_atom atm));
               (prove ~dpos ~dneg fenv exi_senv cs (param_senv, atm), dneg))
             else (
               Debug.print
               @@ lazy
                    ("refuting "
                    ^ Formula.str_of
                        ((*Formula.forall (Set.to_list @@ Atom.term_sort_env_of atm) @@*)
                         Formula.mk_atom atm));
               (dpos, refute ~dpos ~dneg fenv exi_senv cs (param_senv, atm))))
    in
    let dpos, dneg, und =
      if not config.acquire_und then (dpos, dneg, und0)
      else
        (if config.only_diff then d_und else und0)
        |> ExClauseSet.refresh_params exi_senv
        |> ExClauseSet.to_clause_set exi_senv
        |> ClauseSet.resolve_one_step_all ~print:Debug.print
             (Set.Poly.filter_map dpos ~f:ExClause.atom_of_uclause)
             (Set.Poly.filter_map dneg ~f:ExClause.atom_of_uclause)
             exi_senv
        |> Set.Poly.map ~f:fst
        |> ClauseSet.simplify_with
             (Set.Poly.filter_map dpos ~f:ExClause.atom_of_uclause)
             (Set.Poly.filter_map dneg ~f:ExClause.atom_of_uclause)
        |> acquire fenv exi_senv ~dpos ~dneg ~und:und0
    in
    let dpos, dneg, und =
      (if config.resolve_against_problem_clauses then cs else Set.Poly.empty)
      |> ClauseSet.resolve_one_step_all ~print:Debug.print
           (Set.Poly.filter_map d_dpos ~f:ExClause.atom_of_uclause)
           (Set.Poly.filter_map d_dneg ~f:ExClause.atom_of_uclause)
           exi_senv
      |> Set.Poly.map ~f:fst
      |> Set.union
           (if config.unit_prop then Set.filter cs ~f:Clause.is_unit
            else Set.Poly.empty)
      |> ClauseSet.simplify_with
           (Set.Poly.filter_map dpos ~f:ExClause.atom_of_uclause)
           (Set.Poly.filter_map dneg ~f:ExClause.atom_of_uclause)
      |> acquire fenv exi_senv ~dpos ~dneg ~und
    in
    let added =
      Set.diff
        (Set.Poly.union_list [ dpos; dneg; und ])
        (Set.Poly.union_list [ dpos0; dneg0; und0 ])
    in
    Debug.print @@ lazy "*** Example Instances obtained by Resolution:";
    Debug.print
    @@ lazy (String.concat_map_set ~sep:";\n" ~f:ExClause.str_of added);
    Debug.print @@ lazy "";
    let old_examples = VersionSpace.examples_of vs in
    let new_examples = Set.Poly.union_list [ dpos; dneg; und ] in
    Set.iter (Set.diff old_examples new_examples) ~f:(fun ex ->
        ClauseGraph.hide_vertex vs.examples @@ ClauseGraph.mk_example ex);
    let new_examples =
      Set.diff new_examples old_examples
      |> Set.Poly.map ~f:(fun ex ->
          (ex, Set.Poly.singleton (ClauseGraph.Dummy, false)))
      (*TODO: add sources of new_undecided *)
    in
    Ok (State.of_examples vs new_examples)

  let run_phase _iters = resolve
end
