(* Three mechanisms in this subsystem are switched off in every shipped
   configuration -- the index/value cells, the QSAT clause-constraint route
   and the quantifier-prefix synthesis -- and some definitions have no caller
   at all.  Three markers
   say which code is which, and every one of them carries the reason it is
   where it is:

     REACHABLE ON THE DEFAULT PATH -- executes in an ordinary run; the comment
       states what it evaluates to there, which in every case is "no change".
     UNREACHABLE BY DEFAULT (<mechanism>) -- runs only when that mechanism's
       field is set.
     PORTED, UNCALLED -- no caller at all.

   DUBIOUS marks code that is kept without being endorsed: a defect preserved
   deliberately so that unexercised code is not quietly "repaired", a
   heuristic whose constants nothing explains, a printer used as a
   serialiser.  Those are the ones to argue about first. *)

open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open PCSatCommon
open Template.Function

type candidate =
  | Cands of Logic.cand_map * (Logic.cand_map * Ident.tvar) list
  | OutSpace of Ident.tvar list
  | Yield
      (** the phase gave up on this round without proposing anything, so that
          the rest of the loop runs on what is already known.  Its only exits
          otherwise are a candidate and a shape bound that is unset by default,
          so a synthesis that cannot fit the examples never returns and the
          phases after it -- including the resolution that derives new examples
          without needing a candidate -- are never reached again. *)

type candidate_or_unsat_core =
  | Candidate of Logic.cand_map * (Ident.tvar * KindCert.t) list
  | UnsatCore of
      ExClauseSet.t * (Ident.tvar, parameter_update_type Set.Poly.t) Map.Poly.t

type smt_solver_instance = {
  mutable ctx : Z3.context;
  mutable solver : Z3.Solver.solver;
  mutable z3dtenv : (Datatype.t * Z3.Sort.sort) Set.Poly.t;
  mutable z3fenv : (Ident.tvar, Z3.FuncDecl.func_decl) Map.Poly.t;
  mutable smt_timeout : int option;
  mutable has_param_bounds : bool;
      (** whether the template-parameter bounds have been asserted into this
          solver since it was created or renewed. They constrain the parameters
          that a solver's accumulated queries share, so they belong in it once
          per solver -- which is a fact about the solver and not about the
          iteration count, as a module-level counter had it: only the default
          instance ever saw that counter at zero, so the per-target ones ran
          unconstrained and Z3 answered with selector values outside their
          range. *)
  tracked_labels : Z3.Expr.expr list ref;
      (** every label tracked in [solver] since it was created or renewed,
          kept for [synthesis_fresh_solver_per_check], which asks the question
          of a fresh solver under these labels as assumptions *)
}

module Config = struct
  type pex_strategy = Quantify | InstDefault | InstRand of int
  [@@deriving yojson]

  (* How the synthesis query states a goal clause whose body is functional
     predicate applications alone, each to a single variable (the clauses an
     existential becomes once skolemised).  Each application's variable is
     replaced by the predicate's function template; what is left of the
     clause's variables is free in the formula, and a free variable of the
     query is existential to the solver.
     - [Existential]: as it always was, those variables left free.  The query
       then asks only that the clause hold at SOME value of them, a necessary
       condition of the clause (so no solution is excluded), and the solver
       searches values for them alongside the template parameters.
     - [Universal]: those variables bound universally, which is the clause
       itself: the condition is exact.
     - [Omit]: the constraint is not asserted; the clause is still checked by
       validation like every other one, and enters the loop as examples. *)
  type fn_goal_constraint = Existential | Universal | Omit
  [@@deriving yojson]

  type predicate_template =
    | DNF of Template.PredicateDNF.Config.t ext_file
    | Flex of Template.PredicateFlex.Config.t ext_file
    | Arrays of Template.PredicateArrays.Config.t ext_file
  [@@deriving yojson]

  type wf_predicate_template =
    | WF of Template.WFPredicate.Config.t ext_file
    | WF_Flex of Template.WFPredicateFlex.Config.t ext_file
  [@@deriving yojson]

  type fn_predicate_template =
    | FN of Template.FNPredicate.Config.t ext_file
    | FN_Flex of Template.FNPredicateFlex.Config.t ext_file
  [@@deriving yojson]

  type int_function_template =
    | IntFun of Template.IntFunction.Config.t ext_file
    | IntFun_Flex of Template.IntFunctionFlex.Config.t ext_file
  [@@deriving yojson]

  (*type real_function_template =
    | RealFun of Template.RealFunction.Config.t ext_file
    | RealFun_Flex of Template.RealFunctionFlex.Config.t ext_file
  [@@deriving yojson]*)

  type regex_template = RegEx of Template.RegEx.Config.t ext_file
  [@@deriving yojson]

  type t = {
    verbose : bool; [@default false]
    pex_strategy : pex_strategy; [@default InstDefault]
    fn_goal_constraint : fn_goal_constraint; [@default Existential]
    (* [true]: for a *parametric* example atom, do not decide the qualifier
       holes from the truth table on an instantiated copy of the atom; keep the
       qualifiers themselves, applied to the atom's symbolic arguments, so that
       the solver decides them together with the template parameters.  Use with
       [pex_strategy = Quantify], which then binds the parameters that the
       qualifiers mention.  The default [false] keeps the behaviour of forcing
       the holes through the ground truth table, which is provably relatively
       incomplete: there are satisfiable problems it cannot solve and this
       route can.  Ground atoms are
       unaffected either way. *)
    symbolic_holes_for_parametric : bool; [@default true]
    (* [true]: in an example clause, an atom that shares a parameter of a sort
       variable or of a sequence with another atom of the clause is read
       EXACTLY -- its qualifiers kept symbolic, as for the parametric atoms
       above -- with each such parameter one universally bound variable across
       the clause, instead of through that atom's own truth-table row.  The
       row grounds the atom's parameters apart from the other atoms', so a
       candidate that satisfies the clause only through the implication (the
       body atom forces what makes the head true) is rejected at every shape.
       The constraint this builds lies between the per-atom reading and the
       clause, and it is used only when it quantifies no sequence after the
       lengths and literal-index reads of each sequence are abstracted;
       otherwise the per-atom reading is kept ([SharedParams]).  On the cell
       route an atom's celled copies count as that one atom, and only one copy
       of it is read exactly; a read of a literal sequence past its length is
       bound universally, since the theory leaves its value open.  On by
       default: it recovered both sides of an input whose misses were exactly
       this rejection, and on inputs with no such parameter it does nothing
       but allocate, which can still move a solver model through the
       collector. *)
    symbolic_shared_params : bool; [@default true]
    (* [true]: once per run, in a round whose example set is non-empty and has
       no predicate application among any clause's positive atoms, propose
       [false] for every predicate instead of asking the template search
       ([FalseProbe]).  Every such candidate is consistent with those
       examples, and the search has no preference among them: on the cell
       route it returned an unsatisfiable conjunction over an argument the
       fact clause leaves free, so the fact counterexample came back ground
       there where [false] draws it open.  Applies only when every unknown is
       of the ordinary kind.  Sound whatever it proposes, since a candidate is
       validated against the problem.  On by default: over 162 Rust-derived
       inputs at 120 s it gained answers and lost none. *)
    false_probe_on_negative_examples : bool; [@default true]
    (* [true]: a diagnostic that acts on nothing.  Each time the synthesis
       constraints are generated, the solution loaded by the PCSat
       configuration's [load_oracle_sol] is checked against every example
       clause as this synthesizer states it -- for a predicate with cells, the
       celled clause, with the solution's universals restricted to the cells
       each atom offers ([PCSatCommon.OracleProbe]) -- and the first clause it
       violates is printed, with its predicates and their offered cells.  A
       one-line tally per round and the first violation of the run go to
       stderr, the rest through the module's trace.  It tells an example set
       that excludes the intended solution from a search that does not reach
       it.  The run's decisions are unchanged; its checks are extra Z3 queries,
       so they can move the solver's own draws as any extra query can. *)
    oracle_example_probe : bool; [@default false]
    (* [> 0]: in each example clause's synthesis constraint, a positive
       existential (negative universal) that binds a sequence is replaced by
       the disjunction (conjunction) of its instances at the sequence and
       integer literals of its body, their prefixes and suffixes, one literal
       equal to none of them, and the enclosing binders of each other sort, when
       there are at most this many instances ([Ast.SeqExistInst]).  The
       constraint becomes stronger, never weaker: a candidate it yields
       satisfies the examples, and a candidate it excludes may be lost.  It is
       for a guard quantifying over sequences, whose existentials under the
       example's universals left one synthesis query undecided at 100 s where
       the rewritten query answered in half a second.  [0], the default,
       leaves every constraint as it is. *)
    seq_exist_instances : int; [@default 0]
    (* [true]: a hole whose body reads the hole's parameters (a qualifier kept
       symbolic -- route (a), the sort-variable, exact-head, exact-step and
       shared-parameter readings) is substituted into an atom's constraint by
       [Logic.Term.subst_rename_on_capture], one traversal that reduces an
       application by all its arguments at once and renames a binder only
       where it could capture, instead of [Logic.Term.subst], which renames
       every binder it passes and reduces one argument at a time.  The two
       results are alpha-equivalent (the stated contract of both), so the
       constraint is the same up to the names of bound variables; fewer fresh
       names are drawn, which moves later names and so individual CEGIS runs.
       [false], the default, substitutes as before. *)
    hole_subst_rename_on_capture : bool; [@default false]
    (* [true]: the other substitutions of constraint generation -- the
       predicates' templates into an example atom, a clause's grounding
       substitution into its disjunction (whole, or per atom share), and the
       shared-parameter reading's renaming and grounding -- are done by
       [Logic.Term.subst_rename_on_capture] instead of [Logic.Term.subst].
       Each of these terms and maps is beta-normal (templates are lambdas over
       hole applications, groundings map variables to closed terms), which is
       the precondition under which the two are alpha-equivalent; so every
       constraint is the same up to the names of bound variables.  [subst]
       renames every binder it passes with a traversal of its body and
       reduces a template applied to n arguments one argument at a time;
       this does one traversal and draws a fresh name only where a binder
       could capture.  [false], the default, substitutes as before. *)
    cgen_subst_rename_on_capture : bool; [@default false]
    (* [true]: a candidate built from the model keeps, of every template
       [case] whose selector parameter the model sets to an in-range literal,
       only the selected branch ([Logic.select_constant_cases]); the
       candidate is the same function in every model.  A function template
       chooses its result among the hypothesis space's terms of the result
       sort by such a selector, so without it a candidate carries every one
       of those terms, possibly thousands, into each place the candidate is
       substituted (validation's clause questions first), where the
       conversion and simplification reduce them to one.  [false], the
       default, keeps the case whole. *)
    candidate_select_constant_cases : bool; [@default true]
    (* [> 0]: a budget in milliseconds for each validity question the truth
       tables ask while this phase runs -- the rows constraint generation adds
       for new example atoms and the columns a rebuilt hypothesis space adds
       for new qualifiers, each an evaluation against every atom or qualifier
       already there.  A question not decided in time leaves its cell
       undecided and is not recorded as "not valid", so a later question can
       still decide it: answers can be lost, never decided wrongly.  The
       labeling phase has the same field.  [0], the default, asks without a
       budget, as before. *)
    truth_table_valid_timeout : int; [@default 0]
    predicate_template : predicate_template; [@default Common.Util.config_default predicate_template_of_yojson {|["Arrays", ["Filename", "./config/pcsat/template/predicate_arrays_template_cell.json"]]|}]
    wf_predicate_template : wf_predicate_template; [@default Common.Util.config_default wf_predicate_template_of_yojson {|["WF", ["Filename", "./config/pcsat/template/wf_predicate_template.json"]]|}]
    fn_predicate_template : fn_predicate_template; [@default Common.Util.config_default fn_predicate_template_of_yojson {|["FN", ["Filename", "./config/pcsat/template/fn_predicate_template.json"]]|}]
    ne_predicate_template : Template.NEPredicate.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/template/ne_predicate_template.json"]
    adm_predicate_template : Template.AdmPredicate.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/template/adm_predicate_template.json"]
    integ_predicate_template : Template.IntegPredicate.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/template/integ_predicate_template.json"]
    int_function_template : int_function_template; [@default Common.Util.config_default int_function_template_of_yojson {|["IntFun", ["Filename", "./config/pcsat/template/int_function_template.json"]]|}]
    regex_template : regex_template; [@default Common.Util.config_default regex_template_of_yojson {|["RegEx", ["Filename", "./config/pcsat/template/regex_template.json"]]|}]
    update_strategy : TemplateUpdateStrategy.Config.t; [@default TemplateUpdateStrategy.Config.UnsatCore]
    compute_ucores : bool; [@default true]
    qualifier_generator : Qualifier.Generator.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/qualifier/tb.json"]
    extract_qualifiers : bool; [@default true]
    extract_terms : bool; [@default false]
        (** supply the unsat-core qualifier learning with the terms it fits its
            five restricted templates over.  It is the ONLY consumer of those
            terms -- the synthesis template is built with none -- so with this
            off the learning has no material and reports "qualifiers not
            learned" at every round, its qualifier count never moving.  Turning
            it on restores the mechanism and is measured to cost more than it
            buys, because each learning round builds five templates over the
            term set: on a tracked pair the side that answered under the default
            stops answering at 300 s.  The default is therefore the measured
            choice and not an oversight.  When setting it for a measurement,
            set it in the [dbg_] chain as well, since those are copies rather
            than views and a field absent from both leaves nothing to
            notice. *)
    extract_constants : bool; [@default true]
    reduce_quals_terms : bool; [@default false]
    learn_quals_from_ucores : bool; [@default true]
    (* Keep, of the qualifiers learned from an unsat core, only those whose
       free variables are the predicate's parameters.  The learned solution of
       a celled template comes back read as [forall j. phi(x, j, a[j])], and
       taking its atoms strips the quantifier, leaving [j] free under a name
       drawn afresh at every round.  Such an atom can enter no hole -- the
       template generators keep only the qualifiers over the parameters they
       build a template on -- so it adds nothing to the space; but being renamed each round it is never
       equal to one already held, the "nothing new was learned" test never
       fires, and the round never reaches the step that widens the template's
       shape.  A celled run was measured spending a whole 30 s budget in one
       round this way, the qualifier count of one predicate climbing from 82
       to 322 with no growth.  Dropping them changes when the shape grows and
       nothing the template can say, so it cannot bear on the soundness of a
       verdict.  Where the learned solution binds no variable of its own --
       a template with neither cells nor quantified index variables -- no atom
       has such a variable and the switch changes nothing.  On by default:
       over 162 Rust-derived inputs at 120 s it gained answers and lost none. *)
    ucore_quals_params_only : bool; [@default true]
    (* How many extra solver calls a found candidate may spend on having
       fewer qualifier literals; 0 (the default) spends none and keeps the
       first model.  A qualifier hole gives each qualifier an integer key --
       positive takes the qualifier, negative its negation, zero neither --
       and the first model of the synthesis query takes whatever keys the
       solver happened to pick, which is typically almost every qualifier in
       every disjunct: a cube around the examples it was fitted to, true of
       the sample and of little else.  With a positive value the query is
       asked again, in the same solver and with the same constraints, under
       the extra bound "at most [m] keys are nonzero", [m] halving the gap
       between the smallest count found and the largest refuted; each answer
       is a model of the same constraints, so every candidate kept is one the
       unbounded query could have returned. *)
    shrink_candidate_literals : int; [@default 0]
    (* The solver budget of each of those calls, in milliseconds; a call that
       runs out counts as a refutation of its bound. *)
    shrink_candidate_timeout : int; [@default 2000]
    (* Drop a found candidate's qualifier literals one at a time by
       evaluation, with no solver search: each nonzero key is set to zero in
       the model and the change is kept when every constraint of the
       synthesis query that mentions the key still evaluates to [true] under
       the modified model.  Keys whose qualifier mentions an integer literal
       the problem does not are tried first, then the higher-ranked ones.
       Each candidate kept is a model of the same constraints, so it is one
       the query could have returned; validation checks it as any other, and
       soundness is unaffected.  Off by default. *)
    drop_candidate_literals : bool; [@default false]
    (* Build a clause's constraint by keeping its quantifier structure and
       handing it to a solver for quantified formulas, instead of evaluating
       each hole against the truth table.  Off by default; see
       [replace_concrete_clause_with_QSAT], which is unfinished work preserved
       from an abandoned branch. *)
    qsat_clause_constraints : bool; [@default false]
    (* How many celled variants of each example clause to generate (each a
       different sample of the candidate cells); 0 turns the expansion and
       the read-back off.  It is independent of the array template's
       [number_of_cells_per_array], the number of cell columns a template
       binds, with one exception that [instantiate_ext_files] refuses: cell
       columns with no expansion, which leaves the columns in the candidate
       with nothing to convert them and fails at conversion. *)
    celled_examples : int; [@default 0]
    (* Whether an example clause's BODY atoms are expanded at every candidate
       cell instead of at a sample of them.

       The two sides of a clause are not symmetric under the celled reading
       [P(a) = forall j. phi(j, a[j])].  A head atom is satisfied at every
       cell, so any sample of it asks for less than the example does, which
       validation catches.  A body atom is violated at ONE cell, so asserting
       its negation at a sampled cell asks for more: the sample has to contain
       the witness, and where it does not the demand rejects the correct
       solution.  On a prefix-bound invariant that is most of the draws --
       [not (0 <= j) \/ not (j <= i) \/ v <= bound] is true at every index past
       [i], so every candidate cell except the witness refutes the answer.

       Every candidate cell as separate body atoms of one clause is a
       disjunction, hence the weakest sound reading the sample allows: false at
       one of these.  It costs atoms rather than clauses.  It applies only
       where there is one array argument and one cell column, because the
       enumeration is otherwise over tuples and the count is a product; the
       sampled path is kept for the rest. *)
    celled_negative_exhaustive : bool; [@default false]
    (* The same for the HEAD atoms, and it is sound for the opposite reason.
       A head atom asserts [forall j. phi], so phi at every candidate cell is a
       conjunction of consequences -- each implied by what the example says --
       and it is strictly the better approximation, where on the body side
       exhausting was about not being *wrong*.  Left sampled, a head atom
       constrains the candidate at one cell out of six, which is most of why a
       celled run can find a candidate every round and never converge: the
       demand it satisfies is far weaker than the example it came from, so the
       validator refutes it and the loop pays a round for one more cell.

       A conjunction over head atoms is separate CLAUSES, not more atoms in
       one, because several positive atoms of one clause read as a
       disjunction. *)
    celled_positive_exhaustive : bool; [@default false]
    (* Offer, as candidate cells, the integer ARGUMENTS of the example atom
       itself and their two neighbours, beside the indices read off the array.

       The candidates otherwise come from the array a counterexample carries --
       every index it stores, the neighbours of each, and 0..5 -- and a
       constant array stores nothing, so an invariant quantified over a range
       that does not start near zero has no candidate that can be its witness.
       Measured: on [forall j. 10 <= j <= i -> a[j] <= bound] the negative
       example is [I(const 0, 10, -1)], whose only witness is j = 10, the
       candidates are 0..5, and the body side then asks for falsity at six
       cells where the intended invariant holds -- so the examples reject the
       answer and no amount of vocabulary or shape can recover it.

       The predicate's own arguments are where a loop bound is: the invariant
       takes the index it is quantified up to.  This is the cheap half of
       reading the indices off the clause, which is what the design asks for
       and what an example cannot do, since it records the predicate's
       arguments and not the terms its clause read the array at. *)
    cell_candidates_from_args : bool; [@default false]
    (* ... and whether that widening applies to the HEAD side as well as the
       body side.

       The candidate set decides two things at once and they pull in opposite
       directions.  On the body side it is a disjunction -- false at one of
       these -- so a wider set is a WEAKER demand and is what lets a witness in.
       On the head side it is a conjunction -- true at all of these -- so a
       wider set is a STRONGER demand and a heavier query.  Widening it is
       therefore not an improvement but a trade, and it was measured as a clean
       one: taking the atom's own integer arguments as candidates, five runs a
       side, a prefix-bound invariant answers 5 of 5 without it and 0 of 5 with
       it, while one quantified over a range starting at 10 answers 0 of 5
       without and 5 of 5 with.

       Off, the widening is confined to the body side: the head keeps the
       narrow set it had, which is sound because every cell it asks about is
       still one the example's universal implies, and the body gets the wide
       one, which is sound because a disjunction over more cells is weaker.
       There is no reason the two must agree, and a swap is the evidence that
       they should not. *)
    (* Leave a HEAD atom's cell columns as PARAMETERS instead of sampling
       values for them.  Under the concretization a head atom says
       [forall j. P#(j, a[j], x..)], and every choice of sampled j is a
       consequence of that rather than the thing itself, so a candidate that
       holds at the sampled cells and fails elsewhere satisfies every
       constraint the synthesizer was given, is refuted by the validator, and
       comes back as the SAME example: on a two-array input 767 of 801
       counterexamples in one run were one example, while the candidate space
       was nowhere near exhausted.  With the columns left as parameters the
       constraint IS the universal statement -- exact rather than a better
       heuristic -- and the value column is not free either, it is the read
       [select a j] against the counterexample's own array, so nothing is
       invented.  The BODY side must stay ground: its demand is existential
       (some cell falsifies the atom), and a parameter there would read as
       "false at every cell", which is stronger than the example says and
       rejects correct solutions. *)
    (* Offer, as candidate cells, the indices at which the validator's own
       model found a celled candidate to fail.  The abstraction otherwise
       guesses its indices from the array -- stored indices, their neighbours,
       a small prefix -- and an input whose witness is outside that set can
       never be pinned, however many rounds run.  The index is computed one
       phase away and discarded there; [Validator.Config.record_cell_witnesses]
       is what stops discarding it, and both switches are needed for either to
       do anything. *)
    (* Instantiate an array-sorted parameter of a parametric example at an
       array that VARIES, instead of at the dummy.

       An example with parameters means "for every instantiation satisfying the
       condition", so making it ground is a free choice among the values the
       condition admits -- and the dummy for an array sort is a CONSTANT array,
       [const d], which is the one value a learner that reads what the array
       holds can learn nothing from: it holds the same thing at every index, so
       no example over it distinguishes one index from another, and an invariant
       whose content is a relation between indices is unreachable from such
       data. Measured on an input written for exactly that kind of invariant,
       the dominant example is parametric in both arrays and 159 of 337 head
       expansions read [const 0] twice.

       The substitution is applied only to a parameter the example's condition
       does not mention, so the condition's truth at the instance is unchanged
       and the example stays usable; and each parameter gets a different array,
       since giving two of them the same one makes any equation between them
       hold for the wrong reason. *)
    (* How many ground instances one parametric example yields when the
       grounding above is on.  One is a CONSEQUENCE of the example, not the
       example, so a learner may fit the array it was shown and fail on the
       next one -- a hazard the dummy has too and which is merely invisible
       there, since a candidate fitted to a constant array is fitted to
       something that says nothing.  Every instantiation the condition admits
       is sound, so k of them cost nothing in soundness and leave the learner
       constrained by what they have in common, which is the statement.  The
       instance index is applied UNIFORMLY across a clause, because a clause's
       parameters are its atoms' union by name and mixing two instances in one
       clause yields a clause the original does not imply. *)
    celled_array_instances : int; [@default 1]
    celled_varying_array_instances : bool; [@default false]
    (* How many leading indices a varying array actually varies at.  It is a
       number rather than a constant because it is the one place the example
       side and the candidate side can disagree without saying so: the cells a
       candidate is examined at are every stored index with its two neighbours
       and a fixed prefix, so storing at three indices leaves the offered cells
       beyond them reading the array's default -- constant, at exactly the
       indices the abstraction will look. Three is what this did before and is
       kept as the default so the field changes nothing until it is set. *)
    celled_varying_array_width : int; [@default 3]
    (* The sequence counterpart of [celled_varying_array_instances]: ground an
       example clause's parametric SEQUENCE parameters, before the cells are
       read, at a short non-empty literal whose elements differ, instead of
       leaving them to the dummy.  The dummy of a sequence parameter is a
       symbolic constant, whose elements the cell reader cannot state, so the
       atom offers no cell; and where a clause fixes nothing about a sequence
       the cheapest value is the empty one, which offers none either.  The
       literal has [celled_varying_array_width] positions (more to cover the
       clause's integer arguments under [celled_varying_array_at_args]) and at
       most as many as the cell reader offers, so no cell is past its length.
       Sound for the same reason as the array side: any instantiation of a
       parameter no condition mentions is an instance, hence a consequence.
       Uses [celled_array_instances] instances, as the array side does.  Off by
       default. *)
    celled_varying_sequence_instances : bool; [@default false]
    cell_candidates_from_arg_sums : bool; [@default false]
    (* Where [cell_candidates_from_args] offers each integer argument and its
       two neighbours as a candidate cell, also offer the pairwise SUMS of the
       integer arguments.  An invariant [a[k] = b[i+k]] is checked at [k] and at
       [i+k]; the arguments give [k], and without the sums [i+k] is offered only
       if it happens to be stored or in the short prefix -- which on the input
       that asks for it, whose counterexamples carry indices in the thousands,
       it never is.  Only acts where [cell_candidates_from_args] does.
       Measured over 43 cell-route inputs at 30 s: it fires (a cell at [i+k]
       on about a quarter of the celled atoms of the input that asks for it),
       and costs answers -- 21 answered against 23, where the arguments alone
       give 20 -- because every extra candidate multiplies the two-array
       product and heavier synthesis rounds are what that input is short of. *)
    celled_varying_array_growing : bool; [@default false]
    (* Whether the values a varying array stores are drawn from a range that
       grows with the CEGIS round.  Off, they are [seed + n] -- small, and the
       same on every round -- so a candidate that bounds an array's contents by
       a constant fits every grounded instance it is shown and is refuted only
       by the validator, one constant at a time.  On, the [n]-th stored value
       at round [r] is [(seed + n) * (r + 1)], negated at odd [n], so the
       contents spread in both directions as the loop proceeds; and the
       default, read at every index not stored, is nonzero and grows too, with
       its sign alternating between the instances [celled_array_instances]
       asks for, so that a bound of the contents by zero does not fit both
       instances at an index neither stores.  Every third instance gives all the array
       parameters of a clause the SAME array: an atom that must hold for every
       pair of arrays must hold for a pair of equal ones, and without such an
       instance a disequality between two arrays' cells fits every grounded
       head, since arrays seeded by different names differ everywhere.  Every
       instantiation of a parametric example is a consequence of it, so the
       choice of values is sound whatever it is; it decides only what a value
       bound must survive.  With [celled_expansion_cache] on, an expansion
       stored at one round keeps that round's values. *)
    celled_varying_array_at_args : bool; [@default false]
    (* WHERE a varying array varies.  Off, it is the leading indices
       [0 .. width-1], whatever the example is about.  On, it is the integer
       argument values of the clause's atoms and their pairwise sums -- the
       indices an invariant relating two positions, [a[k] = b[i+k]], reads at
       -- falling back to the leading indices where the clause has no integer
       argument.  A dummy that varies at 0-2 while the relation is about
       [k] and [i+k] gives the learner varying arrays that still say nothing
       about the relation.  The indices are the clause's, so every atom of a
       clause grounds a parameter with one array, as soundness requires.
       Measured over 43 cell-route inputs at 30 s: one answer gained and one
       lost, no disagreement.  Where the parametric example the dummy serves is
       a base fact with its counter at 0 -- the common case -- the only integer
       argument is 0, so this varies the array at a single index and cannot
       inform an invariant about index relations there. *)
    cell_candidates_below_zero : int; [@default 0]
    (* How many negative indices, [-1] down to [-m], an integer level offers
       beside what the array offers.  The array's offer is every stored index,
       its two neighbours and the prefix [0 .. 5], so over a constant array --
       which is what a solver returns for an array it is free to choose -- no
       cell is below zero.  A head atom is then demanded true at non-negative
       cells only, a candidate that is false at every negative index satisfies
       it, and the validator refutes that candidate at [-1], one example at a
       time.  Two negative indices, rather than one, give a pair of cells over
       two arrays both orders below zero, which is what a relation between two
       indices ([k = j + i] at [i = 0]) distinguishes.  Sound in both
       directions: an offered cell is an instance of the atom's own universal
       on the head side and one more disjunct on the body side. *)
    cell_candidates_from_cell_values : int; [@default 0]
    (* How many integer VALUES held by an example atom's OTHER celled arrays and
       sequences -- the values at the cells those offer, for a sequence its
       elements at the in-range positions it offers -- an integer index level
       of each array also offers, deduplicated, at most this many; [0] offers
       none.  An invariant that reads one array at a value another holds,
       [q(c, v[k])] with [v] a sequence, is checked at the cell [(c, v[k])],
       and the default offer (stored indices, neighbours, [0..5], integer
       arguments) holds [v[k]] only by luck: where it is missing, a reachable
       state differing from the example only at that cell agrees with it on
       every offered cell, and the goal example then excludes every solution.
       Applies to the exhaustive expansion (body and head) and to the default
       cells of the goal-read expansion, not to the sampled path.

       It changes only WHICH instances an example offers, i.e. which cells the
       synthesis query sees, so it cannot make a verdict unsound: every cell is
       a true index and value of the counterexample's array, an offered cell is
       an instance of the atom's universal on the head side and one more
       disjunct on the body side, and a candidate is still validated against
       the concrete counterexample.  The trade: a weaker demand on the body
       side and a stronger one on the head side, and more instances -- with two
       arrays the product grows by up to this many per level -- so larger
       synthesis queries and more atoms past [celled_product_bound]. *)
    cell_witness_indices : bool; [@default false]
    celled_head_parametric : bool; [@default false]
    (* Which form the parametric head takes.  [true] writes the value column as
       the read against the counterexample's own array, which is the statement
       itself and is measured UNUSABLE -- the synthesis query becomes
       [exists holes. forall j. phi] and the two inputs that answered 4 of 4 and
       5 of 5 give no verdict at 90 s.  [false] splits the domain instead: the
       array is a constant plus finitely many stores, so the stored indices are
       covered by the ground expansion and only the complement needs a
       quantifier, where the value column is the array's DEFAULT and no longer a
       term in [j] at all.  For one cell column the split is exact; for several
       it covers the tuples whose components are all outside the stored set and
       is a weakening on the mixed ones, which is still stronger than sampling.
       Kept as a switch rather than deleted because the two forms answer the
       same question and only a measurement separates them. *)
    celled_head_parametric_full : bool; [@default false]
    (* Neither form above states its head exactly, whatever [pex_strategy]
       says, and for one reason: a template hole is replaced by the truth
       table's value of each qualifier at the atom's ROW, and the row of a
       parametric atom is taken after [ExAtom.instantiate] has put every
       parameter -- each cell index among them -- at its default point.  The
       universal [Quantify] wraps round the clause then binds variables no hole
       mentions, and a head [forall j. P#(j, a[j], x..)] is asked only at
       [j = 0].  On top of that the example's own array parameters are grounded
       before the cells are read.  A candidate true at index 0 and false at 1
       satisfies such a constraint, the validator returns the same parametric
       example, and the loop repeats it round after round.

       With this on, the head of a clause that has one parametric head atom and
       no body keeps the example's parameters as variables, reads each cell
       against the atom's own array argument ([CellArray.exact_parametric_cells])
       and evaluates every hole at that atom SYMBOLICALLY -- the qualifier is
       left as a formula over the parameters, not looked up in the table -- so
       under [Quantify] the constraint is [forall p j. phi(t(p), j, t(p)[j])],
       which a candidate satisfies exactly when its read-back satisfies the
       example.  Under any other [pex_strategy] the parameters are substituted
       by their defaults again and this buys nothing.  A clause of any other
       shape, or an atom whose array is a sequence, keeps the paths above. *)
    celled_head_exact : bool; [@default false]
    (* Keep the guard of an example atom whose every parameter the default
       instance turned into a dummy constant.  The instance [cond => P(t)] at
       those constants still has [cond] over them, and a dummy constant stands
       for any element, so [cond] is not decided there: [$1 <> $2] becomes
       [dummy_$1 <> dummy_$2].  With this off the cell expansion reads such an
       atom as the bare [P(t)], which demands [P] also where the constants are
       equal -- more than the example says, so a true solution can violate the
       synthesis constraint.  The candidates are still validated, so this
       costs solutions and never soundness.  On, such an atom is expanded from
       its parametric form, with the parameters and the guard it had. *)
    celled_keep_instance_guards : bool; [@default true]
    (* The exact form of a STEP example, [N(u1) => P(u2)] with one celled
       atom on each side, where [N] and [P] are read back as
       [forall j. phi(x.., j, a[j])].  Its meaning is
         (forall k. phi_N(x1, k, t1[k]))  =>  forall j. phi_P(x2, j, t2[j]).
       The head is a universal demand, so its cell indices stay variables [j],
       bound universally whatever [pex_strategy] says.  The body is a
       universal premise, so it is instantiated: at the head's own indices [j]
       (the FRAME instance, through which a cell the step does not touch
       carries its fact across) and at the integer arguments of the two atoms
       and their pairwise sums (standing in for the indices the step clause
       reads), every tuple of those being one more body atom of the same
       clause.  Instantiating a premise only weakens it, so a candidate that
       meets the result meets the example exactly, and the validator cannot
       return that example against it again.  In the other direction nothing
       is lost for a solution of the problem whose candidate is extensible (a
       partial array meeting the instances extends to a total one meeting the
       universal), provided the clause reads its arrays only at indices in
       that set.  The ordinary expansion samples the body's indices without
       the frame instance and is neither a weakening nor a strengthening of
       the example.  Arrays are read at symbolic indices through their
       concrete [store] chains, so the query stays over integers.  Any other
       shape -- a sequence, a curried array, more than one atom on a side, a
       product of instances past [celled_product_bound] -- falls back to the
       ordinary expansion. *)
    celled_step_exact : bool; [@default false]
    (* With [celled_step_exact], write each instantiated group of hole
       entries of an exact step example once ([PCSatCommon.HoleNaming]): a
       hole's entries are grouped by the argument positions their qualifiers
       read, each group instance (hole, positions, the arguments there) gets
       a fresh Boolean name and each compound argument of an atom read by
       route (a) a fresh name of its sort, the holes' bodies become
       conjunctions of names, and the clause binds each name it reaches
       universally with the disjunct [name xor definition] or
       [name <> definition].  The constraint is EQUIVALENT to the one with
       the hole bodies written out, so the synthesis query has the same
       models over the template parameters and the candidates are unchanged;
       the names are bound inside the constraint and reach no model.  Such
       an example has dozens of atoms differing in one cell, each
       instantiating every hole entry with its [ite] and [store] chains
       copied into each qualifier occurrence: one example's constraint was
       0.5-1.2 million nodes before conversion, and 0.16-0.26 million with
       the names.  Applies where the template applies each hole to its own
       parameters only, and to a constraint read under [Quantify] or
       [InstDefault] (not the shared-parameter reading); elsewhere the
       constraint is built as before. *)
    celled_step_exact_name_groups : bool; [@default false]
    (* Expand the body atom of a GOAL example -- an example clause with no
       positive atom -- at the cells its own clause read, when the validator or
       the resolver recorded them ([Validator.Config.record_goal_reads],
       [SMTResolver.Config.record_goal_reads]; the reads are kept in the side
       table [GoalReads], never in the example).

       Under the read-back [N(x, a) := forall k. phi(x, k, a[k])] a goal
       example [N(t)] means [exists k. not phi(t, k, t[k])], and its synthesis
       constraint is the disjunction of [not phi] over some set of cells of
       [t].  Any such disjunction implies the example, so this switch cannot
       make the loop accept a candidate the example refutes.  What the set
       decides is whether a SOLUTION can meet the constraint: a reachable
       state agreeing with [t] on every offered cell excludes every solution
       from the round the example arrives.  The default offer (stored indices,
       neighbours, 0..5) misses the witness whenever the clause refutes the
       state far from it -- a read [b[i + k]] with a model's [i] in the
       thousands -- while the tuple of the clause's own reads is exactly the
       witness.  An exact record replaces the default cells by its read tuple
       (an array the clause does not read keeps its default cells); a record
       from a clause with a head is added to the default cells.  A record whose
       product, or the union over records, exceeds [celled_product_bound]
       falls back to the ordinary expansion. *)
    celled_goal_at_reads : bool; [@default true]
    (* Offer a positive example's head, in the exhaustive expansion, also at
       the indices its refutations named: the index at which a candidate's
       read-back failed in the head of the clause that produced the example
       ([Validator.Config.record_head_witnesses] records them, beside the
       example, in [GoalReads]).  Over a constant array the head is otherwise
       demanded at the prefix [0 .. 5] alone, so a candidate false only below
       zero or past it meets the example, the validator refutes it with the
       same point, and the loop repeats that round without end.  A head cell
       is an instance of the example's own universal, so an added cell is one
       more consequence of the example: it never excludes a solution, and it
       is never offered to a body atom.  Off, or with nothing recorded, the
       expansion is the one it was. *)
    celled_head_at_witnesses : bool; [@default false]
    (* At most this many extra cell tuples per body atom of a GOAL example --
       an example clause with no positive atom -- beside whichever expansion
       the atom got (at the recorded reads, exhaustive, or sampled); [0] adds
       none.  From each tuple the expansion produced, a variant moves a
       sequence cell to another in-range position, and then one index level of
       an array cell: an integer level to a value the tuple's own cells hold,
       one of the atom's integer arguments, or one of [-1 .. -m] ([m] is
       [cell_candidates_below_zero], at least 1); any other level to a term of
       its sort the atom's arguments reach -- see
       [CellArray.goal_cell_variants].

       Why: the constraint of a goal example is the disjunction of [not phi]
       over its offered tuples, and a solution is excluded outright when the
       tuple where it fails is not offered.  Two shapes miss it: an invariant
       [q(c, v[k])] reading one array at a value a sequence holds fails at the
       pair (position [k], index [v[k]]), and an index bound [j >= 0] over a
       constant array fails only at a negative [j].  The exhaustive product
       falls back to one sampled tuple past [celled_product_bound], and the
       recorded reads name only the indices the clause read, so neither pair
       is offered by construction.  Every variant is a true cell tuple of the
       counterexample's arrays and only adds a disjunct to the example's body,
       so it cannot make a verdict unsound; it costs synthesis-query size. *)
    celled_goal_value_variants : int; [@default 0]
    (* With [celled_goal_value_variants] on: order the variants so that those
       pairing an array cell's integer index with the value a sequence cell of
       the same tuple holds come before the limit cuts the list.  That pair is
       where [q(c, v[k])] fails, and it is two or three moves from a base
       tuple, so with several arrays and argument terms the plain order fills
       the limit before reaching it.  Order only: the variants are the same
       true cell tuples, so soundness is that of the field above. *)
    celled_goal_linked_variants_first : bool; [@default false]
    (* With [celled_goal_value_variants] on: offer the variants to the BODY
       atoms of a clause with a positive atom too.  A step example
       [N(u1) => P(u2)] under the read-back [forall cells. phi] means
       [(exists cells. not phi_N) \/ P(u2)], and the expansion writes the body
       as a conjunction of [N] at its offered tuples, so every added tuple is
       one more disjunct [not phi_N] and only weakens the demand; the head is
       left as it was.  Why: a lower bound [j >= 0] on a produced value over a
       constant array fails only at a negative index the body never offers,
       and a step whose head's accumulator took that value then demands the
       bound's violation of every candidate that keeps the bound. *)
    celled_step_body_value_variants : bool; [@default false]
    cell_candidates_from_args_in_head : bool; [@default false]
    (* How many (index, value) tuples the exhaustive expansion may build for one
       atom.  It enumerates the PRODUCT of every array's candidates, because an
       invariant relating two arrays is refuted at a pair of indices and drawing
       each array's cell independently finds the witness only by luck; the
       product is therefore the point and also the cost.  Past the bound the
       atom falls back to the sampled path, which is weaker and sound. *)
    celled_product_bound : int; [@default 64]
    (* Where a BODY atom's product is over [celled_product_bound], offer a
       sweep instead of one sampled tuple: every array held at the cell the
       sampler draws for it (the same draw, so the sampled tuple is among the
       offered ones) and each array in turn ranging over all of its candidate
       cells -- [sum_k |C_k| - (m - 1)] tuples for [m] arrays where the product
       has [prod_k |C_k|].  And an atom that declines no longer sends the
       clause's OTHER body atoms to sampling: each atom whose product fits is
       still expanded exhaustively.

       Why: body atoms are premises, so the offered tuples read as the
       disjunction of [not phi] over them, and one sampled tuple is the
       strongest such constraint -- it excludes every candidate that holds at
       that tuple even when it fails at another the exhaustive expansion would
       have offered.  An intended invariant relating a cell of one array to a
       cell of another at an offset is then excluded whenever the sample is
       not at that offset, and the template grows instead.  The sweep's
       disjunction contains the sample's and is contained in the product's, so
       the switch admits only candidates the sampled fallback rejected, and
       never one the exhaustive expansion would reject.  The head side is
       untouched: a head atom's tuples are separate demands, so sampling there
       weakens rather than strengthens. *)
    celled_over_bound_sweep : bool; [@default true]
    (* The HEAD-side counterpart of [celled_over_bound_sweep], for the
       exhaustive head expansion ([celled_positive_exhaustive]): where a head
       atom's product of cell candidates is over [celled_product_bound], offer
       the sweep's tuples (the sampled tuple, and each array in turn ranging
       over all of its candidates with the others at the sample) instead of
       sending every head atom of the clause back to one sampled tuple.

       Contract.  Head atoms are demands, so each offered tuple is one more
       variant clause, and every tuple is a true cell (index, value) of the
       counterexample's arrays, hence an instance of the head's universal
       [forall j. phi]: the variants are consequences of the example, so a
       solution is never excluded, and the sweep contains the sampled tuple,
       so the demand is never weaker than the fallback's.  An atom whose
       product fits is expanded exhaustively as before; an atom that offers no
       cell, or whose sweep is itself over [m * celled_product_bound] tuples
       for [m] arrays, still sends the clause to the sampler.

       Why: a step counterexample [N(t) => P(t')] over two arrays, each storing
       a few indices, has a head product just over the bound (99 for 64), and
       one sampled tuple is rarely where the refuted candidate fails.  The
       candidate then meets every example the counterexample produced, the
       synthesizer proposes it again, and a repeat read as non-progress grows
       the template instead -- three to four disjuncts for an invariant that
       needs one, at ten times the synthesis cost per round. *)
    celled_head_over_bound_sweep : bool; [@default false]
    (* Take the candidate cells from the atom's own integer arguments ALONE,
       instead of adding them to what the array offers.

       The two are different claims about where an index worth speaking about
       comes from.  The array's offer -- every index it stores, the neighbours
       of each, and 0..5 -- is a guess made without looking at the problem, and
       it is a product once there is more than one array: two arrays at seven
       candidates each is forty-nine tuples per example atom.  The predicate's
       own arguments are where a loop bound and an offset actually are, and
       they are the cheapest approximation of the design's intent, which is to
       read the indices off the CLAUSE.

       It is a narrowing and can therefore lose a witness the array's offer
       would have caught, so it is a switch and not a default; what it buys is
       the size of the product, which is measured to be what stops an input
       with two arrays. *)
    cell_candidates_from_args_only : bool; [@default false]
    (* Give a predicate's SEQUENCE arguments cells as well as its arrays: a
       sequence of a scalar reachable from the parameters becomes a cell path
       with one integer index, its cells are the positions below its length,
       and a candidate learned over them is read back as [forall j. 0 <= j <
       seq.len s => phi(j, seq.nth s j, ..)], the range being the premise that
       makes every read denote something.  This setting decides the path list
       for the template as well as for the example expansion -- the template's
       own field of the same name is overwritten with it -- because the two
       must agree on which paths there are.  On by default: it changes the
       template of every predicate over a sequence under a cell chain, and
       nothing outside a cell chain. *)
    sequence_cells : bool; [@default true]
    (* With [sequence_cells], give every sequence one extra cell, the SENTINEL
       at index -1 holding the element sort's plain constant, so that a
       candidate [phi] is read back as [phi(-1, d, x..) /\ forall j. 0 <= j <
       seq.len s => phi(j, seq.nth s j, x..)].  Without it every candidate is
       true on the empty sequence, and a counterexample making the predicate
       false there is met by none of them.  The same setting lets the
       template keep the qualifiers that speak of a sequence only through its
       length ([i < seq.len s]) when it otherwise keeps only cell qualifiers,
       since the sentinel instance is where such a fact is stated; the
       template's own field of that name is overwritten with it.  On by
       default; it changes nothing unless [sequence_cells] is on. *)
    sequence_sentinel_cell : bool; [@default true]
    (* When a candidate learned over cells does not use one cell -- neither its
       index nor its value column occurs in the formula -- read the candidate
       back without that cell's universal, which is then vacuous.  The
       rewrite is an equivalence: [forall j. phi] with [j] not free in [phi]
       is [phi] over a non-empty index sort; with a sequence's range premise
       it is [phi] when the sentinel makes the premise satisfiable at [-1],
       and [seq.len s <= 0 \/ phi] otherwise.  What it changes is the query
       the validator hands to the solver: a candidate relating whole sequences
       with no cell in it is read back quantifier-free, where the unrewritten
       form nests one universal per sequence around it and the solver was
       seen not to return on a recursive clause over three such sequences.
       On by default. *)
    readback_drops_unused_cells : bool; [@default true]
    (* Keep only the tuples whose indices differ by one of the atom's own
       integer arguments, instead of every tuple of the product.

       This is the cheap half of the design's intent, which is to take the
       indices from the CLAUSE.  A clause relating two arrays does not mention
       an unrelated pair of indices: "this slice is that one from index i on"
       reads them at [k] and [i + k], so every tuple it names satisfies the
       relation the invariant is about, while a product is mostly tuples that
       do not.  Whether the relation or merely the size is what matters was
       unmeasured, and this is the switch that asks.

       It narrows the body side, so it can drop the tuple that would have been
       the witness and is a heuristic rather than a refinement -- the same
       standing as the candidate set it filters. *)
    celled_tuples_related : bool; [@default false]
    (* Collapse the candidate indices of a CONSTANT array level into classes
       before the exhaustive expansion builds its cells.  Over such a level
       every cell holds the same value, so two cells differ only by their
       index, and two indices standing in the same order to every comparison
       the candidate space can make with the index column are
       indistinguishable to every candidate; one representative per class
       then states exactly what the whole list states, and the synthesis query
       shrinks by the rest.

       It is exact and not a heuristic, but only where the space's reading of
       the index column is known: every qualifier of the predicate's holes must
       compare the column linearly with terms the example fixes, and the
       template must not mention the column outside its holes -- an affine
       atom with synthesized coefficients separates any two integers.  Where
       either fails for an atom, that atom is expanded in full.  It is also
       not applied where [celled_tuples_related] filters a product of several
       arrays, since that filter judges pairs of concrete indices and a
       representative need not stand in the relation its class-mates do. *)
    celled_collapse_constant_indices : bool; [@default false]
    (* The same collapse over a level that STORES values at some indices.
       Every candidate index that is not stored at such a level reads the
       level's default, so among the non-stored indices two cells differ only
       by their index, as over a constant level, and are collapsed by the same
       criterion; every stored index keeps its own cell, and a non-stored index
       is never merged with a stored one.  A level whose stored indices are not
       all integer literals, or with a function or a parameter array above or
       at it, is not collapsed.  It covers constant levels too, so it collapses
       them whether or not [celled_collapse_constant_indices] is set.  For the
       last level, whose non-stored cells all hold the default, the default is
       substituted for the value column when the forms are computed, so a
       qualifier comparing index and value together does not refuse the level
       merely because the stored cells hold other values. *)
    celled_collapse_default_indices : bool; [@default false]
    (* Reuse an example clause's celled expansion across synthesis attempts
       instead of rebuilding it on every attempt, the unsat-core restarts
       included, which re-expand the same examples many times over.  Only an
       expansion that drew nothing from the cell sampler is reused, so the
       constraints an attempt receives are the ones it would have built -- up
       to the names of the fresh index variables a parametric head expansion
       binds -- and the sampler's stream is not moved.  An OCaml-side saving
       only; the query the solver receives is unchanged. *)
    celled_expansion_cache : bool; [@default false]
    (* Let the solver choose each template's quantifier prefix -- which of its
       index variables are universal and in what order -- instead of taking
       the [forall i_1..i_n] the template generated.  It needs a template that
       binds indices ([number_of_quantifiers_per_array]) and the clause
       constraints to carry the marker ([qsat_clause_constraints]); with
       neither it has nothing to choose and nothing changes. *)
    synthesize_quantifier_prefix : bool; [@default false]
    (* ACTS ON LEVEL 3 of the failure policy -- what the structure growth is
       told to grow, when the qualifier learning of level 2 has failed.

       After this many consecutive unsat cores whose labels blame neither the
       coefficients nor the constants, blame them anyway.  The shape search
       reacts only to the labels the core carries, so a bound that no core
       mentions is never raised however long the search runs.  0 is off, and
       the constants are relaxed 500 times more rarely than the coefficients,
       a ratio taken from the work this comes from rather than measured here.

       A LAST RESORT, and measured not to be aimed at the cause.  Probing
       where those two labels are *produced* rather than where they arrive:
       the main synthesis call emits neither, ever, because the array
       template's ordinary arm asks for zero affine atoms with no bounds, so
       no such constraint exists for a core to name; the only producer is the
       last of the five unsat-core attempts, which does carry them, rarely --
       once in one benchmark's whole run, four times in 157 in another.  So
       the labels are scarce rather than missing, and forcing one in makes
       the search raise a bound the template it will next generate does not
       use.  Before reaching for this, ask instead whether that arm should
       have affine atoms at all: without them an array predicate can only say
       disjunctions of the qualifiers it is handed. *)
    force_bound_blame_after : int; [@default 0]
    (* ACTS ON THE HANDOVER FROM LEVEL 2 TO LEVEL 3: when no qualifier-learning
       attempt succeeds, which of their blame maps reaches the structure
       growth.

       When no unsat-core attempt teaches a qualifier, which attempt's blame
       drives the template widening.  [false], the default, uses the **last**
       attempt's map and discards the other five -- including the one from the
       template actually in use, which is what the [ToDo] in the loop below
       names.  [true] unions them all per predicate.

       It is off because it is measurably *inert*, not because it costs
       anything.  Instrumented, the union was compared with the last attempt's
       map at every firing -- 66 firings over fifteen CHC files -- and they were
       **identical every time**.  Two reasons, and both are worth knowing before
       changing this: the five variant templates are built over the same
       hypothesis space and the same examples, so their cores blame the same
       predicates with the same labels; and the primary template's extra blame
       is [Qual], which the label-to-action table in the array template maps to
       **no action at all**.  Consistent with the corpus differential, which
       found 0 verdict disagreements and no answer gained or lost over 120 files.
       (That run also reported 1.13x wall.  With the maps identical the merge
       cannot be its cause, and no same-binary control was taken for it, so that
       number says nothing and is not a reason for anything.)

       So the [ToDo] this answers describes a real gap in principle -- the map
       from the template actually in use is among the discarded -- and an
       unobservable one in practice.  Whoever makes [Qual] act should measure
       this again, because that is what would make the primary map carry
       something the variants do not. *)
    blame_from_every_qualifier_attempt : bool; [@default false]
    widen_from_core_after_learning_timeout : bool; [@default false]
        (** when every qualifier-learning attempt of a failed round came back
            without a qualifier and the last one's labels are [TimeOut] alone
            (that attempt's query timed out), grow the shape from the latest
            earlier core that blamed something -- an earlier attempt's, or the
            candidate search's own -- instead of from the timeout, which no
            template module acts on, so the shape would never grow.  Off,
            nothing changes. *)
    smt_timeout : int option; [@default Some 16000]
    keep_timeout_budget_across_rebuild : bool; [@default false]
        (** when the synthesis query times out, the templates are regenerated
            with the same shape over the same examples (every template module
            ignores the timeout label), and renewing the solver instances puts
            the configured [smt_timeout] back -- so the doubled budget set at
            the timeout is never read and the same query is asked again at the
            same budget.  On, a rebuild caused only by such a timeout keeps
            each instance's doubled budget, capped by
            [max_synthesis_timeout]; any other rebuild returns to
            [smt_timeout].  Off, nothing changes. *)
    reask_on_timeout_without_rebuild : bool; [@default false]
        (** when the first synthesis query of a round (the one over the
            qualifiers in hand) times out and the answer teaches nothing
            else, ask the same solver the same question again at the doubled
            budget, capped by [max_synthesis_timeout], instead of regenerating
            every template and example constraint only to ask it again.  The
            re-ask asserts nothing new, so the candidates it admits are those
            of the first ask; it is repeated while the budget can still grow,
            and a timeout at the cap, or any other answer, goes on as before.
            Off, nothing changes. *)
    max_synthesis_timeout : int option; [@default None]
        (** the cap on that kept budget, in milliseconds; [None] means four
            times [smt_timeout].  Read only with
            [keep_timeout_budget_across_rebuild] or
            [reask_on_timeout_without_rebuild] on. *)
    synthesis_arith_solver : int option; [@default Some 2]
        (** Z3's [smt.arith.solver] for the synthesis query (and its one-shot
            attempt): [Some 2] asks it with the simplex-based [theory_arith]
            instead of the default [lp]-based [theory_lra]
            ([Z3interface.arith_solver_key]).  The question is the same and
            both decide linear arithmetic, so only its time can change.  On
            template-coefficient queries the default spent its time in bound
            propagation and the tableau, and the older solver decided them 5
            to 30 times faster.  [None], the default, leaves the parameter
            unset. *)
    synthesis_oneshot_first_ms : int; [@default 0]
        (** a budget in milliseconds for asking each synthesis query first of
            a fresh, non-incremental solver and using its model when it
            answers [sat]; anything else falls through to the incremental
            check with its unsat core, unchanged.  Z3's incremental mode skips
            the one-shot preprocessing, and on template-coefficient queries
            over many witness templates it was seen heavy-tailed: queries a
            one-shot check answers in under a second took 16 s or more.  0
            asks only the incremental solver. *)
    synthesis_fresh_solver_per_check : bool; [@default false]
        (** ask every check of the incremental synthesis solver of a fresh
            solver holding the same assertions, under the tracked labels as
            assumptions ([Z3interface.incr_check_sat_unsat_core
            ~fresh_labels]).  The question, its models and its unsat cores are
            those of the incremental check; what changes is that no state of
            the earlier checks is carried into it.  On quantified synthesis
            constraints the incremental solver was seen to come back undecided
            ([unknown], or out of its budget, and then re-asked at doubled
            budgets) on questions a fresh solver answers in 1-2 s, while every
            check pays the internalisation of the whole query. *)
    synthesis_fresh_solver_after_undecided : bool; [@default false]
        (** ask the incremental synthesis solver first, as without the field,
            and only a question it leaves undecided ([unknown], a timeout) of a
            fresh solver as [synthesis_fresh_solver_per_check] does, once, at
            the same budget.  A decided answer is the incremental one; the
            fresh one is the same question.  Ignored when
            [synthesis_fresh_solver_per_check] is on. *)
    sync_threshold : int option; [@default None]
    restart_threshold : int option; [@default Some 20]
    non_progress_up_to_bound_names : bool; [@default true]
        (** compare this round's candidate with the last one up to the names
            of every bound variable ([PCSatCommon.CandidateEquiv]), not only
            the outer lambda parameters, when deciding that the round made no
            progress.  A candidate read back from a quantified template carries
            binders named afresh at every read-back, so the plain comparison
            never finds two such candidates equal and the non-progress update
            of the templates never fires for them.  Observed on a two-clause
            array problem under three disjuncts and no restart threshold: 1,400
            to 1,600 rounds in 120 s, the template never renewed, 99 of 217
            traced rounds proposing the candidate of the round before up to the
            name of its quantified index.  On by default; firing the update
            changes the search wherever a quantified candidate repeats. *)
    extracted_terms_mention_a_param : bool; [@default true]
        (** keep an extracted term only when it mentions one of the predicate's
            own parameters.

            A term that mentions none of them is CLOSED, and the qualifiers the
            generator builds over a closed term are closed too -- so each takes
            the same value at every example of that predicate and separates no
            two of them, while still enlarging the space and the synthesis
            query.  The ground facts a solution does need are extracted from the
            clauses directly and are present either way.

            Measured on a four-clause datatype problem whose solution is
            [P(x) := (tl nil = nil) /\ x in 0..3]: with the extraction on and
            this filter off, two closed terms take the space from 9 qualifiers
            to 14 and the run never answers at 45 s, widening the shape to 85
            disjuncts; with the filter on it is 9 qualifiers again and [sat,2]
            in under a second, three runs of three.  The qualifier the solution
            needs is among the nine in both cases.

            [true] by default, and it can only bite where [extract_terms] is on,
            which is not the shipped default -- so this changes no shipped
            configuration and exists because it may be what makes that flag
            affordable.  A sort test was tried first and is WORSE for the same
            benefit: it drops every datatype term, and a predicate over a
            datatype wants the testers and equalities built from one.  What this
            keeps that a sort test would not is a datatype term involving a
            parameter, [is_cons (tl x)] and the like. *)
    max_extracted_terms : int option; [@default None]
        (** at most this many terms in the qualifier learning's vocabulary, per
            predicate, smallest first.

            The vocabulary is every compound non-Boolean top-level term of every
            qualifier the predicate has, and it was unbounded.  Measured over ten
            predicates it is 4, 6, 8, 8, 8, 12, 14, 15, 44 and 100 terms -- a
            factor of twenty-five -- which is why the bound is per predicate and
            not global.

            [None] by default, which is the vocabulary as it was.  What it does
            and does not buy is measured, over 37 files, three settings and three
            builds of one logic that differ only in where the fresh-name counter
            starts, one run per cell with the address layout pinned.  There are
            two regimes and this field addresses one of them.  Where it bites
            (18 files with more than twenty terms) switching the vocabulary on
            costs 1.73x wall and a bound of twenty costs 1.21x, so it recovers
            about seventy per cent of the cost and loses no answer.  Where it is
            inert (19 files with twenty or fewer) the vocabulary costs 3.81x and
            the bound necessarily costs the same -- and every answer lost in the
            whole sweep, four of 57 runs, is in that half.

            So the bound is worth having for cost and is NOT the remedy for the
            lost answers: on the file that loses its answer outright, a bound of
            ONE loses it too.  Size is not what is expensive there; having any
            vocabulary at all is, because these terms reach the hypothesis space
            and not only the learning.  See the comment at the extraction itself.

            Smallest first because a term's size is the only ordering available
            without asking what the failure was about, and a smaller term is
            cheaper for the affine templates the learning fits.  It is
            deterministic, which matters: the set's own order is by the names
            inside the terms, and those move whenever a fresh variable is drawn.
        *)
    widen_shape_with_learning : bool; [@default false]
        (** grow the structural parameters in an iteration where the qualifier
            learning DID learn something, as well as in one where it did not.

            The synthesizer has two moves when it cannot fit its examples --
            enlarge the vocabulary a candidate may use, and enlarge the shape it
            may take -- and they are not symmetric.  Learning reports whether it
            changed anything; growing the shape is unconditional and its only
            failure is a template leaving a bound that is unset in every shipped
            configuration.  So "try the other one first" names no program, and
            the shipped policy -- spend the whole vocabulary budget, then take
            one structural step -- is the only order the asymmetry admits.

            This is the alternative that is well defined: take both moves on
            every failure, so that neither budget is spent before the other.  It
            matters because the ratio is otherwise a consequence rather than a
            choice: measured over four files of one corpus, learning fires 21
            times against 4 failures on one and 5 against 86 on another, so a
            policy that ties the structural budget to learning's failures hands
            those two wildly different budgets.

            [false] by default, which is the behaviour this phase has always
            had.  Which policy is better is a question about a corpus and not
            about this code, and nothing here answers it. *)
    yield_after_failures : int option; [@default None]
        (** return [Yield] after this many consecutive rounds in which the
            examples could not be fitted and the templates were grown instead.
            [None], the default, never yields, which is the behaviour this phase
            has always had: its only other exits are a candidate and a shape
            bound that is itself unset by default, so a synthesis that cannot fit
            the examples spins inside the phase and the later phases stop running
            -- measured at 706 candidate searches against 9 completed rounds on
            one input.  Yielding hands the round on so that validation, labeling
            and resolution run on what is already known; resolution derives new
            examples without needing a candidate, and it is reached only when
            this phase returns. *)
  }
  [@@deriving yojson]

  let instantiate_ext_files cfg =
    let open Or_error in
    (match cfg.predicate_template with
      | DNF cfg ->
          Template.PredicateDNF.Config.load_ext_file cfg
          >>= fun predicate_template -> Ok (DNF predicate_template)
      | Flex cfg ->
          Template.PredicateFlex.Config.load_ext_file cfg
          >>= fun predicate_template -> Ok (Flex predicate_template)
      | Arrays cfg ->
          Template.PredicateArrays.Config.load_ext_file cfg
          >>= fun predicate_template -> Ok (Arrays predicate_template))
    >>= fun predicate_template ->
    (* cells in the template need the example expansion: a template with cell
       columns and [celled_examples = 0] keeps the columns in its candidate,
       and converting that candidate raises ("failed to convert term") *)
    (match predicate_template with
    | Arrays arrays -> (
        match ExtFile.unwrap arrays with
        | Ok (a : Template.PredicateArrays.Config.t)
          when a.number_of_cells_per_array > 0 && cfg.celled_examples <= 0 ->
            error_string
            @@ sprintf
                 "the array template's number_of_cells_per_array is %d but \
                  the synthesizer's celled_examples is %d: cells need \
                  celled_examples > 0 (or number_of_cells_per_array = 0)"
                 a.number_of_cells_per_array cfg.celled_examples
        | _ -> Ok ())
    | _ -> Ok ())
    >>= fun () ->
    (match cfg.wf_predicate_template with
      | WF cfg ->
          Template.WFPredicate.Config.load_ext_file cfg
          >>= fun wf_predicate_template -> Ok (WF wf_predicate_template)
      | WF_Flex cfg ->
          Template.WFPredicateFlex.Config.load_ext_file cfg
          >>= fun wf_predicate_template -> Ok (WF_Flex wf_predicate_template))
    >>= fun wf_predicate_template ->
    (match cfg.fn_predicate_template with
      | FN cfg ->
          Template.FNPredicate.Config.load_ext_file cfg
          >>= fun fn_predicate_template -> Ok (FN fn_predicate_template)
      | FN_Flex cfg ->
          Template.FNPredicateFlex.Config.load_ext_file cfg
          >>= fun fn_predicate_template -> Ok (FN_Flex fn_predicate_template))
    >>= fun fn_predicate_template ->
    Template.NEPredicate.Config.load_ext_file cfg.ne_predicate_template
    >>= fun ne_predicate_template ->
    Template.AdmPredicate.Config.load_ext_file cfg.adm_predicate_template
    >>= fun adm_predicate_template ->
    Template.IntegPredicate.Config.load_ext_file cfg.integ_predicate_template
    >>= fun integ_predicate_template ->
    (match cfg.int_function_template with
      | IntFun cfg ->
          Template.IntFunction.Config.load_ext_file cfg
          >>= fun int_function_template -> Ok (IntFun int_function_template)
      | IntFun_Flex cfg ->
          Template.IntFunctionFlex.Config.load_ext_file cfg
          >>= fun int_function_template ->
          Ok (IntFun_Flex int_function_template))
    >>= fun int_function_template ->
    (*(match cfg.real_function_template with
    | RealFun cfg ->
        Template.RealFunction.Config.load_ext_file cfg
        >>= fun real_function_template -> Ok (RealFun real_function_template)
    | RealFun_Flex cfg ->
        Template.RealFunctionFlex.Config.load_ext_file cfg
        >>= fun real_function_template ->
        Ok (RealFun_Flex real_function_template))
    >>= fun real_function_template ->*)
    (match cfg.regex_template with
      | RegEx cfg ->
          Template.RegEx.Config.load_ext_file cfg >>= fun regex_template ->
          Ok (RegEx regex_template))
    >>= fun regex_template ->
    TemplateUpdateStrategy.Config.instantiate_ext_files cfg.update_strategy
    >>= fun update_strategy ->
    Qualifier.Generator.Config.load_ext_file cfg.qualifier_generator
    >>= fun qualifier_generator ->
    Ok
      {
        cfg with
        predicate_template;
        wf_predicate_template;
        fn_predicate_template;
        ne_predicate_template;
        adm_predicate_template;
        integ_predicate_template;
        int_function_template;
        regex_template;
        update_strategy;
        qualifier_generator;
      }

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "SolutionTemplate"
    let instantiate = instantiate_ext_files
  end)

  module type ConfigType = sig
    val config : t
  end
end

(* The qualifiers of [quals] whose free variables are all among [params].
   Precondition: [quals] are atoms taken out of a learned solution, so a
   variable the solution bound under a quantifier may occur free in them.
   Postcondition: a subset of [quals]; a qualifier over [params] alone is
   kept, and so is one that has no free variable at all.  Used when reading
   an unsat core's solution back as qualifiers: a variable that is not a
   parameter is one no template hole can bind, so the qualifier adds nothing
   to the space, and since such variables are renamed at every round it would
   also never be recognised as already learned. *)
let params_only_quals ~(params : sort_env_list) quals =
  Templ.quals_over_set quals params

(* An example clause's constraint, assembled from per-atom parts that can be
   shared between clauses.

   The constraint of an example clause whose atoms give the terms [a1 .. an]
   (n >= 2, none of them the literal [true] or [false]) under the parameters
   [params], with [sub] grounding some of them, is

     reference = Evaluator.simplify (to_old_fml {} temp_param_senv
                   (forall params (subst sub (or_of [a1; ..; an]))))

   The celled expansion turns one example into a dozen clauses that differ in
   their head and share their body, so that expression was converted,
   simplified and scanned for the theory of strings once per head variant, over
   the same dozens of body atoms each time -- most of what a heavy constraint
   generation spent once the hole substitution had been made cheap.  Here each
   atom's share of it is computed once ([derive]) and a clause pays only for
   combining the shares ([assemble]).

   Why the result is [reference] itself, step by step (each step is the code
   of the function named):
   - [Logic.Term.subst] rebuilds an application node from its substituted
     children, and [or_of]'s nodes apply the constant [Or], which is not a
     lambda, so the substituted chain is the chain of the substituted atoms;
   - [Logic.Term.mk_binds] (under [forall]) keeps, in order, the parameters
     free in the body, and [Logic.Term.fvs_of] of an application is the union
     of its children's;
   - [to_old_formula] converts a binder by extending the environment and an
     [Or] node by converting both children under the same environment and
     joining them with the raw [Formula.mk_binop]; an atom's conversion reads
     the environment only at the variables occurring in it, so extending it
     with just the parameters free in that atom gives the same formula;
   - [Evaluator.simplify] of a chain of [Or] nodes is [simplify_or] of the
     union, over the chain's leaves ([disj_leaves]), of [disjuncts_of] of each
     leaf simplified; the union is a set, so how it is grouped does not
     matter, and [simplify_or] folds over it in element order;
   - [Evaluator.simplify] of [Bind (Forall, [x], body)] simplifies the body and
     then either merges [x] into a [Forall] the body became or wraps it;
     [shell] below is that code, applied innermost binder first.
   The one thing that can differ is fresh names: an atom's share is computed at
   its first occurrence and reused, so a name its simplification or
   substitution draws (a binder renamed by [subst]; there is none on the cell
   route, whose templates bind nothing) is drawn once instead of once per
   clause, and later names move.

   Postcondition of [assemble]: the formula described above, and a flag that is
   [true] only when that formula contains neither a free variable of string
   sort nor a string constant -- the question the caller asks to decide whether
   to eliminate if-then-else.  Every variable and function symbol of
   [simplify_or]'s result occurs in the set it was given (a grouped comparison
   is rebuilt over the same two terms, or becomes [true]), and a binder only
   removes variables, so a set whose elements have neither gives a result with
   neither.  The flag is [false] whenever some element has one, even if
   simplification removed it, and the caller then asks the question itself. *)
(* The search behind [shrink_candidate_literals], apart from the solver so it
   can be tested.  [ask m] is a model whose count is at most [m], or [None]
   when the bound is refuted or the call ran out of budget; [count] reads a
   model's count.  Contract: given [model] with [count model = n0], the result
   is [model] or a model returned by [ask], its count is at most [n0], and
   [ask] is called at most [max_calls] times.  Each call halves the gap
   between the best count found and the largest bound refuted, so with
   enough calls the result is minimal among what [ask] can return. *)
module ShrinkSearch = struct
  let run ~max_calls ~count ~ask model =
    let rec go calls model hi lo =
      if calls >= max_calls || hi - lo <= 1 then (model, hi)
      else
        let mid = lo + ((hi - lo) / 2) in
        match ask mid with
        | Some model' ->
            let n' = count model' in
            (* a model over the bound would break the monotone descent; keep
               the one in hand *)
            if n' > mid then go (calls + 1) model hi mid
            else go (calls + 1) model' n' lo
        | None -> go (calls + 1) model hi mid
    in
    go 0 model (count model) (-1)
end

(* The search behind [drop_candidate_literals], apart from the solver so it
   can be tested.  [keys] are a candidate's nonzero keys in the order to try;
   [holds zeroed ks] says whether the model with every key of [zeroed] set to
   zero still satisfies the constraints ([ks] are the keys just added to
   [zeroed], disjoint from the ones accepted before, so an implementation
   may re-check only what mentions them).
   With [~blocks:true] (the default) the first pass asks about blocks: the
   whole list first, and a rejected block is split into halves, left before
   right, down to single keys; a single key rejected is kept.  When a left
   half is accepted whole, its right half as a whole would be the question
   just rejected, so it is split without being asked.  With [~blocks:false]
   the first pass asks about each key alone, in order.  Either way a key
   rejected before a later drop is tried again alone in a further pass,
   because a constraint that is not monotone in its literals (a cell guard,
   a hole in a clause body) can accept one zero only after another.
   Contract, for an oracle that accepts the empty set and answers by the set
   it is asked about:
   - [zeroed] is a subset of [keys] and [kept] is the rest, in order;
   - [zeroed] is empty or a set [holds] accepted, so the modified model
     satisfies whatever the original did;
   - when [irredundant] is [true], every kept key was last rejected against
     [zeroed] itself, so no single kept key can be dropped; it is [false]
     only when [max_passes] ran out first;
   - the first pass asks at most [2 |keys| - 1] questions ([|keys|] exactly
     without blocks), and each further pass at most one per key still kept;
   - for a monotone oracle (the accepted sets closed under subsets) with [m]
     keys kept, every rejected block holds a key that ends kept, so the first
     pass asks at most [1 + 2 m ceil(log2 |keys|)] questions, and the result
     is the one asking about each key alone gives.
   Every candidate kept is a model of the same constraints as the one it
   replaces, so soundness is unaffected: validation checks every candidate. *)
module DropSearch = struct
  let run ?(max_passes = 3) ?(blocks = true)
      ~(holds : 'k Set.Poly.t -> 'k list -> bool) (keys : 'k list) =
    let zeroed = ref Set.Poly.empty and drops = ref 0 and calls = ref 0 in
    (* a kept key carries the number of drops made when it was last
       rejected: it is stale, and worth trying again, once more were made *)
    let kept_rev = ref [] in
    let ask ks =
      incr calls;
      let zeroed' = Set.union !zeroed (Set.Poly.of_list ks) in
      if holds zeroed' ks then (
        zeroed := zeroed';
        drops := !drops + List.length ks;
        true)
      else false
    in
    let keep k = kept_rev := (k, !drops) :: !kept_rev in
    (* [known_rejected]: this block is exactly the set last rejected *)
    let rec block ~known_rejected (a : 'k array) lo hi =
      let len = hi - lo in
      if len > 0 then
        let accepted =
          (not known_rejected) && ask (Array.to_list (Array.sub a ~pos:lo ~len))
        in
        if not accepted then
          if len = 1 then keep a.(lo)
          else
            let mid = lo + (len / 2) in
            let before = !drops in
            block ~known_rejected:false a lo mid;
            (* the left half accepted whole leaves the right half the
               question this block was rejected on *)
            block ~known_rejected:(!drops - before = mid - lo) a mid hi
    in
    if blocks then block ~known_rejected:false (Array.of_list keys) 0 (List.length keys)
    else List.iter keys ~f:(fun k -> if not (ask [ k ]) then keep k);
    let kept = ref (List.rev !kept_rev) in
    let passes = ref 1 in
    let stale () = List.exists !kept ~f:(fun (_, s) -> s < !drops) in
    while stale () && !passes < max_passes do
      incr passes;
      kept :=
        List.filter_map !kept ~f:(fun (k, s) ->
            if s < !drops then if ask [ k ] then None else Some (k, !drops)
            else Some (k, s))
    done;
    (!zeroed, List.map !kept ~f:fst, not (stale ()), !calls, !passes)
end

(* A Z3 formula over a few integer constants, read once into an OCaml tree
   so that [drop_candidate_literals] can evaluate it under many assignments
   without a solver call each time.  [of_expr ~key] reads the Boolean and
   arithmetic connectives and gives [None] on anything else (division,
   arrays, datatypes, quantifiers, an uninterpreted application), for which
   the caller treats the formula as one it cannot evaluate; [key] maps a
   constant to its index, [None] for a constant the tree may not contain.
   [holds values t] is the value of [t] with constant [i] read as
   [values.(i)], in exact rational arithmetic, so it agrees with Z3's reading
   of every connective accepted; [None] when [t] is not Boolean or reads a
   constant whose value is [None]. *)
module KeyEval = struct
  type t =
    | Num of Q.t
    | Bool of bool
    | Key of int
    | App of Z3enums.decl_kind * t list

  type v = VN of Q.t | VB of bool

  exception Unsupported

  let of_expr ~key e =
    let memo = Hashtbl.create (module Int) in
    let rec go e =
      let ast = Z3.Expr.ast_of_expr e in
      let i = Z3.AST.get_id ast in
      match Hashtbl.find memo i with
      | Some t -> t
      | None ->
          let t =
            if
              (not (Z3.AST.is_expr ast))
              || Z3.AST.is_var ast || Z3.AST.is_quantifier ast
            then raise Unsupported
            else if Z3.Arithmetic.is_int_numeral e then
              Num (Q.of_bigint (Z3.Arithmetic.Integer.get_big_int e))
            else if Z3.Arithmetic.is_rat_numeral e then
              Num
                (Q.make
                   (Z3.Arithmetic.Integer.get_big_int
                      (Z3.Arithmetic.Real.get_numerator e))
                   (Z3.Arithmetic.Integer.get_big_int
                      (Z3.Arithmetic.Real.get_denominator e)))
            else
              let kind = Z3.FuncDecl.get_decl_kind (Z3.Expr.get_func_decl e) in
              match kind with
              | OP_TRUE -> Bool true
              | OP_FALSE -> Bool false
              | OP_UNINTERPRETED when Z3.Expr.is_const e -> (
                  match key e with Some k -> Key k | None -> raise Unsupported)
              | OP_AND | OP_OR | OP_NOT | OP_IMPLIES | OP_ITE | OP_EQ
              | OP_DISTINCT | OP_XOR | OP_LE | OP_LT | OP_GE | OP_GT | OP_ADD
              | OP_SUB | OP_MUL | OP_UMINUS | OP_TO_REAL ->
                  App (kind, List.map (Z3.Expr.get_args e) ~f:go)
              | _ -> raise Unsupported
          in
          Hashtbl.set memo ~key:i ~data:t;
          t
    in
    try Some (go e) with
    | Unsupported -> None
    | exn_ when not (Common.Timer.is_async exn_) -> None

  (* one connective applied to its arguments' values *)
  let apply kind (args : v Lazy.t list) =
    let b x = match Lazy.force x with VB b -> b | VN _ -> raise Unsupported in
    let n x = match Lazy.force x with VN q -> q | VB _ -> raise Unsupported in
    let equal x y =
      match (Lazy.force x, Lazy.force y) with
      | VB x, VB y -> Bool.(x = y)
      | VN x, VN y -> Q.equal x y
      | _ -> raise Unsupported
    in
    match ((kind : Z3enums.decl_kind), args) with
    | (OP_AND | OP_OR), _ ->
        (* read every argument, so that the value does not depend on their
           order: the absorbing value wins, then an argument with no value *)
        let absorbing = Stdlib.(kind = OP_OR) in
        let vs = List.map args ~f:(fun x -> try Some (b x) with Unsupported -> None) in
        if List.exists vs ~f:(function Some v -> Bool.(v = absorbing) | None -> false)
        then VB absorbing
        else if List.exists vs ~f:Option.is_none then raise Unsupported
        else VB (not absorbing)
    | OP_NOT, [ x ] -> VB (not (b x))
    | OP_IMPLIES, [ x; y ] -> VB ((not (b x)) || b y)
    | OP_XOR, [ x; y ] -> VB Bool.(b x <> b y)
    | OP_ITE, [ c; x; y ] -> if b c then Lazy.force x else Lazy.force y
    | OP_EQ, [ x; y ] -> VB (equal x y)
    | OP_DISTINCT, _ ->
        let rec all_distinct = function
          | [] -> true
          | x :: rest ->
              List.for_all rest ~f:(fun y -> not (equal x y))
              && all_distinct rest
        in
        VB (all_distinct args)
    | OP_LE, [ x; y ] -> VB Q.(n x <= n y)
    | OP_LT, [ x; y ] -> VB Q.(n x < n y)
    | OP_GE, [ x; y ] -> VB Q.(n x >= n y)
    | OP_GT, [ x; y ] -> VB Q.(n x > n y)
    | OP_ADD, _ ->
        VN (List.fold args ~init:Q.zero ~f:(fun acc t -> Q.add acc (n t)))
    | OP_MUL, _ ->
        VN (List.fold args ~init:Q.one ~f:(fun acc t -> Q.mul acc (n t)))
    | OP_SUB, x :: rest ->
        VN (List.fold rest ~init:(n x) ~f:(fun acc t -> Q.sub acc (n t)))
    | OP_UMINUS, [ x ] -> VN (Q.neg (n x))
    | OP_TO_REAL, [ x ] -> VN (n x)
    | _ -> raise Unsupported

  let rec eval values = function
    | Num q -> VN q
    | Bool b -> VB b
    | Key i -> (
        match values.(i) with Some v -> v | None -> raise Unsupported)
    | App (kind, args) ->
        apply kind (List.map args ~f:(fun t -> lazy (eval values t)))

  let holds values t =
    try match eval values t with VB b -> Some b | VN _ -> None
    with Unsupported -> None

  (* The same tree with each node's value under a current assignment kept,
     and a pointer to its parent, so that the value after changing a set of
     constants is recomputed along the union of the paths to them only.
     [cur] is [None] where the node has no value (an ill-formed node, a
     constant with no value, or one below it). *)
  type inc = {
    node : t;
    args : inc array;
    mutable parent : inc option;
    mutable pos : int;  (** its index among its parent's [args] *)
    (* for a conjunction or disjunction: how many arguments currently have
       the absorbing value ([false] for a conjunction) or no value, so that
       changing some arguments costs those arguments and not all of them *)
    mutable nhit : int;
    mutable nnone : int;
    mutable cur : v option;
    mutable dirty : bool;
    mutable dirty_args : int list;
  }

  (* The compiled trees of one assignment: each live constant's leaves, and
     what [update] changed, for [commit] or [rollback] *)
  type forest = {
    leaves : (int, inc list) Hashtbl.t;
    mutable undo : (inc * v option * int * int) list;
    mutable saved : (int * v option) list;
    mutable updated : int;  (** nodes recomputed so far, a cost measure *)
  }

  let forest () =
    { leaves = Hashtbl.create (module Int); undo = []; saved = []; updated = 0 }

  let value_of f = try Some (f ()) with Unsupported -> None

  let mk node args cur =
    { node; args; parent = None; pos = 0; nhit = 0; nnone = 0; cur;
      dirty = false; dirty_args = [] }

  let absorbing_of kind = Stdlib.(kind = Z3enums.OP_OR)

  let classify absorbing = function
    | Some (VB b) when Bool.(b = absorbing) -> `Hit
    | Some (VB _) -> `Pass
    | _ -> `None

  (* [live i] says which constants may change later; a subtree with none
     below it is folded to its value and its children dropped, so the result
     holds only the paths to a live constant, whose leaves are registered in
     [forest] *)
  let compile ?(forest = forest ()) ~live values t =
    let rec go t =
      match t with
      | Num _ | Bool _ -> (mk t [||] (value_of (fun () -> eval values t)), false)
      | Key i ->
          let c = mk t [||] values.(i) in
          if live i then (
            Hashtbl.add_multi forest.leaves ~key:i ~data:c;
            (c, true))
          else (c, false)
      | App (kind, ts) ->
          let cs = List.map ts ~f:go in
          let args = Array.of_list (List.map cs ~f:fst) in
          let has_live = List.exists cs ~f:snd in
          let cur =
            value_of (fun () ->
                apply kind
                  (Array.to_list
                     (Array.map args ~f:(fun a ->
                          lazy
                            (match a.cur with
                            | Some v -> v
                            | None -> raise Unsupported)))))
          in
          if not has_live then (mk (Bool false) [||] cur, false)
          else
            let c = mk t args cur in
            Array.iteri args ~f:(fun p a ->
                a.parent <- Some c;
                a.pos <- p);
            (match kind with
            | OP_AND | OP_OR ->
                let absorbing = absorbing_of kind in
                Array.iter args ~f:(fun a ->
                    match classify absorbing a.cur with
                    | `Hit -> c.nhit <- c.nhit + 1
                    | `None -> c.nnone <- c.nnone + 1
                    | `Pass -> ())
            | _ -> ());
            (c, true)
    in
    fst (go t)

  (* recompute a node marked dirty from its arguments, recording what it was *)
  let rec reeval forest values n =
    if not n.dirty then n.cur
    else (
      forest.undo <- (n, n.cur, n.nhit, n.nnone) :: forest.undo;
      forest.updated <- forest.updated + 1;
      let v =
        match n.node with
        | Key j -> values.(j)
        | Num _ | Bool _ -> n.cur
        | App (((OP_AND | OP_OR) as kind), _) ->
            let absorbing = absorbing_of kind in
            List.iter n.dirty_args ~f:(fun p ->
                let c = n.args.(p) in
                (match classify absorbing c.cur with
                | `Hit -> n.nhit <- n.nhit - 1
                | `None -> n.nnone <- n.nnone - 1
                | `Pass -> ());
                match classify absorbing (reeval forest values c) with
                | `Hit -> n.nhit <- n.nhit + 1
                | `None -> n.nnone <- n.nnone + 1
                | `Pass -> ());
            if n.nhit > 0 then Some (VB absorbing)
            else if n.nnone > 0 then None
            else Some (VB (not absorbing))
        | App (kind, _) ->
            (* every argument is recomputed first, so that the whole path is
               cleaned however the connective short-circuits *)
            let vs = Array.map n.args ~f:(reeval forest values) in
            value_of (fun () ->
                apply kind
                  (Array.to_list
                     (Array.map vs ~f:(fun v ->
                          lazy (match v with Some v -> v | None -> raise Unsupported)))))
      in
      n.cur <- v;
      n.dirty <- false;
      n.dirty_args <- [];
      v)

  (* [update forest values changes] sets each [values.(i)] to its new value
     and recomputes every node above a changed live constant, each once; it
     returns the roots so recomputed.  Contract: afterwards every node's
     [cur] is its value under [values]; [commit] keeps that, [rollback]
     restores the nodes and [values] as they were before the [update]. *)
  let update forest values changes =
    let roots = ref [] in
    let rec mark n =
      if not n.dirty then (
        n.dirty <- true;
        match n.parent with
        | None -> roots := n :: !roots
        | Some p ->
            p.dirty_args <- n.pos :: p.dirty_args;
            mark p)
    in
    List.iter changes ~f:(fun (i, v) ->
        forest.saved <- (i, values.(i)) :: forest.saved;
        values.(i) <- v;
        List.iter (Hashtbl.find_multi forest.leaves i) ~f:mark);
    List.iter !roots ~f:(fun r -> ignore (reeval forest values r));
    !roots

  let commit forest =
    forest.undo <- [];
    forest.saved <- []

  let rollback forest values =
    List.iter forest.undo ~f:(fun (n, cur, nhit, nnone) ->
        n.cur <- cur;
        n.nhit <- nhit;
        n.nnone <- nnone);
    List.iter forest.saved ~f:(fun (i, v) -> values.(i) <- v);
    commit forest

  let holds_root (n : inc) =
    match n.cur with Some (VB b) -> Some b | _ -> None
end

(* The universal reading of a goal clause over functional predicates, as the
   synthesis query states it under [fn_goal_constraint = Universal].
   [close ~uni_senv fml] binds universally, in one block at the top, exactly
   the free term variables of [fml] that [uni_senv] (the clause's own
   variables) names, and leaves every other free variable (a template
   parameter) free.
   Contract: no variable of [uni_senv] is free in the result; the free
   variables outside [uni_senv] are those of [fml]; the result implies [fml]
   in every model (it is [fml]'s closure over those variables), and is [fml]
   itself, physically, when [fml] has no such variable. *)
module FnGoalClosure = struct
  let close ~uni_senv fml =
    Formula.mk_forall_if_bounded
      (Set.to_list
      @@ Set.filter (Formula.term_sort_env_of fml)
           ~f:(fst >> Map.Poly.mem uni_senv))
      fml
end

module DisjunctionAssembly = struct
  (* One atom's share of the constraint: the disjunct set it contributes after
     conversion and simplification, the free variables of its substituted
     term (which decide the parameters the clause binds), and whether any of
     those disjuncts mentions the theory of strings. *)
  type derived = {
    leaves : Formula.t Set.Poly.t;
    fvs : Ident.tvar Set.Poly.t;
    stringy : bool;
  }

  (* The question [cgen]'s caller asks of a constraint, per disjunct.  A
     failure to answer counts as "may mention strings", which only sends the
     caller back to asking the question of the whole formula. *)
  let stringy_disjunct phi =
    try
      Set.exists (Formula.term_sort_env_of phi) ~f:(snd >> Term.is_string_sort)
      || Set.exists (Formula.funsyms_of phi) ~f:(function
           | T_string.StrConst _ -> true
           | _ -> false)
    with exn_ when not (Common.Timer.is_async exn_) -> true

  (* [subst] is [Logic.Term.subst] or a substitution alpha-equivalent to it
     on beta-normal input; the share is then the same up to bound names. *)
  let derive ?(subst = fun env t -> Logic.Term.subst env t) ~temp_param_senv
      ~(params : Logic.sort_env_list) ~sub term =
    let term = match sub with None -> term | Some sub -> subst sub term in
    let fvs = Logic.Term.fvs_of term in
    let env =
      List.fold params ~init:temp_param_senv ~f:(fun env (x, s) ->
          if Set.mem fvs x then Map.Poly.set env ~key:x ~data:s else env)
    in
    let leaves =
      Set.Poly.union_list
      @@ List.map ~f:(fun leaf ->
             Formula.disjuncts_of @@ Evaluator.simplify leaf)
      @@ Evaluator.disj_leaves []
      @@ Logic.ExtTerm.to_old_fml Map.Poly.empty env term
    in
    { leaves; fvs; stringy = Set.exists leaves ~f:stringy_disjunct }

  (* [Evaluator.simplify]'s binder case for a [Forall] over one variable,
     applied to the already simplified body, innermost binder first. *)
  let shell (params : Logic.sort_env_list) body =
    List.fold_right params ~init:body ~f:(fun (x, s) r ->
        let bound = [ (x, Logic.ExtTerm.to_old_sort s) ] in
        match r with
        | Formula.Bind (Formula.Forall, bounds', phi'', _) ->
            Formula.mk_bind Formula.Forall (bounds' @ bound) phi''
        | r -> Formula.mk_bind Formula.Forall bound r)

  (* [parts] are the atoms' shares; see the postcondition above. *)
  let assemble ~(params : Logic.sort_env_list) (parts : derived list) =
    let ftv = Set.Poly.union_list @@ List.map parts ~f:(fun d -> d.fvs) in
    let bounds = List.filter params ~f:(fst >> Set.mem ftv) in
    ( shell bounds @@ Evaluator.simplify_or @@ Set.Poly.union_list
      @@ List.map parts ~f:(fun d -> d.leaves),
      not (List.exists parts ~f:(fun d -> d.stringy)) )

  (* What [assemble] stands for, for the checks that compare the two. *)
  let reference ~temp_param_senv ~(params : Logic.sort_env_list) ~sub terms =
    let phi = Logic.BoolTerm.or_of terms in
    Evaluator.simplify
    @@ Logic.ExtTerm.to_old_fml Map.Poly.empty temp_param_senv
    @@ Logic.BoolTerm.forall params
    @@ match sub with None -> phi | Some sub -> Logic.Term.subst sub phi

  (* The precondition on the terms: at least two, and none a Boolean literal,
     which [or_of] would drop or stop at. *)
  let applicable terms =
    List.length terms >= 2
    && List.for_all terms ~f:(function
         | Logic.Con ((Logic.BoolTerm.True | Logic.BoolTerm.False), _) -> false
         | _ -> true)
end

module type SolutionTemplateType = sig
  (*val initialize : unit -> unit*)
  val synthesize : int -> State.u -> candidate
  val init_incr : unit -> unit
end

module Make
    (RLCfg : RLConfig.ConfigType)
    (Cfg : Config.ConfigType)
    (APCSP : PCSP.Problem.ProblemType) : SolutionTemplateType = struct
  let config = Cfg.config
  let id = PCSP.Problem.id_of APCSP.problem

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id

  module TemplateUpdateStrategy :
    TemplateUpdateStrategy.TemplateUpdateStrategyType =
    TemplateUpdateStrategy.Make
      (RLCfg)
      (struct
        let config = config.update_strategy
      end)
      (APCSP)

  module QualifierGenerator =
    Qualifier.Generator.Make
      (struct
        let config = ExtFile.unwrap_or_abort config.qualifier_generator
      end)
      (APCSP)

  let extracted_qualifiers =
    if not config.extract_qualifiers then Map.Poly.empty
    else
      Map.Poly.fold (PCSP.Problem.senv_of APCSP.problem) ~init:Map.Poly.empty
        ~f:(fun ~key:(Ident.Tvar name) ~data:sort acc ->
          let args =
            LogicOld.sort_env_list_of_sorts
            @@ List.map (Logic.Sort.args_of sort) ~f:Logic.ExtTerm.to_old_sort
          in
          let quals =
            Common.PhaseTime.with_phase "generate-extracted" @@ fun () ->
            Set.Poly.map ~f:snd
            @@ QualifierGenerator.generate (Ident.Pvar name) args Set.Poly.empty
                 (Map.Poly.empty, ClauseGraph.create ())
                 0
          in
          Map.Poly.add_exn acc ~key:(Ident.Pvar name) ~data:(args, quals))

  let extracted_terms =
    if not config.extract_terms then Map.Poly.empty
    else
      Map.Poly.map extracted_qualifiers ~f:(fun (args, phis) ->
          ( args,
            (* The terms the *qualifier learning* fits atoms over.  Concretely:
               every qualifier this predicate has is a candidate atom such as
               [i <= len(s)], and what is kept here is the compound non-Boolean
               TOP-LEVEL TERMS occurring in those -- [len(s)], [i + 1], [x * 2].
               The learning then fits affine combinations of them as new atoms,
               which is the half of the language the synthesis template cannot
               express, since its holes are filled with qualifiers rather than
               built from terms.  Calling this set a "vocabulary" is convenient
               and misleading: it is a set of terms, and its size is a count of
               terms, not of predicates or of symbols.

               They are NOT private to it, and a comment here used to say they
               were -- that the synthesis template is built with no terms at all
               for an ordinary predicate, so nothing here reaches it and nothing
               here widens what the synthesizer can propose.  Measured, the set
               reaches the hypothesis space: on a four-clause datatype problem
               the space goes from 9 qualifiers and 0 terms to 14 qualifiers and
               8 terms, and the loop from one hypothesis-space update answering
               `sat` in 0.4 s to 204 updates and no answer at 45 s.  The
               qualifier generator expands these terms, so they widen the space
               the synthesizer searches as well as the one learning fits.

               That is why the cost of switching this on is not a function of how
               MANY terms there are: on the file above a bound of ONE loses the
               answer exactly as an unbounded vocabulary does, and switching the
               learning itself off does not give it back.

               Only each qualifier's top-level terms are collected.  Neither
               every subterm (74 terms become 150 on one predicate) nor each
               term with its additive constant removed (74 become 114) would
               serve a purpose: the reason for either is to put an atom within
               the synthesis template's reach, which these terms cannot do, and
               a missing atom is supplied on the qualifier side instead.  With
               the plain extraction the learning works: on an input where the
               learning otherwise reports that it learned nothing, it learns,
               and the synthesizer's unsat cores fall from 348 to 1. *)
            let param_vs = Set.Poly.of_list @@ List.map args ~f:fst in
            let all =
              Set.filter ~f:(fun t ->
                  Fn.non Term.is_bool_sort (Term.sort_of t)
                  && Term.is_compound (*ToDo*) t
                  && ((not config.extracted_terms_mention_a_param)
                     || not (Set.are_disjoint (Term.tvs_of t) param_vs)))
              @@ Set.concat_map phis ~f:Formula.terms_of
            in
            Debug.print
            @@ lazy (sprintf "vocabulary before bound: %d" (Set.length all));
            match config.max_extracted_terms with
            | Some n when Set.length all > n ->
                Set.Poly.of_list @@ List.take
                  (List.sort (Set.to_list all) ~compare:(fun t1 t2 ->
                       let c = Int.compare (Term.ast_size t1) (Term.ast_size t2) in
                       if c <> 0 then c
                       else String.compare (Term.str_of t1) (Term.str_of t2)))
                  n
            | _ -> all ))

  let extracted_consts =
    if not config.extract_constants then Map.Poly.empty
    else
      let str_consts =
        Set.concat_map (PCSP.Problem.old_formulas_of APCSP.problem)
          ~f:(fun phi ->
            Set.Poly.filter_map (Formula.funsyms_of phi) ~f:(function
              | T_string.StrConst _ as fsym -> Some (Term.mk_fsym_app fsym [])
              | _ -> None))
      in
      Map.Poly.mapi extracted_qualifiers ~f:(fun ~key ~data:(_, phis) ->
          Set.union str_consts
          @@ Set.concat_map ~f:(function
            | T_int.Int n
              when Z.(Compare.(n <> zero && n <> one && n <> minus_one)) ->
                Set.Poly.of_list [ T_int.mk_int n; T_int.mk_int Z.(-n) ]
            | T_real.Real r when Q.(r <> zero && r <> one && r <> minus_one) ->
                Set.Poly.of_list [ T_real.mk_real r; T_real.mk_real Q.(-r) ]
            | T_bv.BVNum (size, i)
              when let bits = T_bv.bits_of size in
                   Z.(Compare.(i <> zero && i <> one && i <> bvneg bits one)) ->
                Set.Poly.of_list
                  [
                    T_bv.mk_bvnum ~size i;
                    T_bv.mk_bvnum ~size (bvneg (T_bv.bits_of size) i);
                  ]
            | T_string.StrConst _ as fsym ->
                Set.Poly.singleton (Term.mk_fsym_app fsym [])
            | _ -> Set.Poly.empty (*ToDo*))
          @@ Set.concat_map ~f:Formula.funsyms_of
          @@
          if true then phis
          else
            (if true then
               Set.filter ~f:(fun phi -> Set.mem (Formula.pvs_of phi) key)
             else Fn.id)
            @@ PCSP.Problem.old_formulas_of APCSP.problem)

  (* The absolute value of every integer literal the (preprocessed) problem
     mentions, including those inside the arguments of a predicate application,
     where no extracted qualifier sees them.  The absolute value because
     normalization moves a bound to one side: [x >= 11] is printed and stored
     as [0 <= -11 + x].  Forced only by a template that asks for it. *)
  let problem_int_consts =
    lazy
      (Set.to_list
      @@ Set.concat_map (PCSP.Problem.old_formulas_of APCSP.problem)
           ~f:(fun phi ->
             Set.Poly.filter_map (Formula.funsyms_of phi) ~f:(function
               | T_int.Int n -> Some (T_int.mk_int (Z.abs n))
               | _ -> None)))

  (* the problem's constraints, forced only by a template that reads the
     array writes they perform *)
  let problem_formulas =
    lazy (Set.to_list (PCSP.Problem.old_formulas_of APCSP.problem))

  (* the problem's clauses, forced only by a template that reads its
     self-loops *)
  let problem_clauses =
    lazy
      (match PCSP.Problem.clauses_of_opt APCSP.problem with
      | None -> []
      | Some cls ->
          Set.to_list
          @@ ClauseSet.to_old_clause_set (PCSP.Problem.senv_of APCSP.problem) cls)

  let template_modules :
      (Ident.tvar, (module Template.Function.Type)) Map.Poly.t =
    Map.Poly.mapi (PCSP.Problem.senv_of APCSP.problem)
      ~f:(fun ~key:tvar ~data ->
        let module Arg = struct
          let name = tvar

          let sorts =
            List.map ~f:Logic.ExtTerm.to_old_sort @@ Logic.Sort.args_of data

          let fenv = PCSP.Problem.fenv_of APCSP.problem
          let sol_space = PCSP.Problem.sol_space_of APCSP.problem
          let id = id
          let with_cond = PCSP.Problem.is_adm_pred_with_cond APCSP.problem tvar
          let nwf_tag = PCSP.Problem.nwf_tag_of APCSP.problem tvar
          let problem_int_consts = problem_int_consts
          let problem_formulas = problem_formulas
          let problem_clauses = problem_clauses

          (* over [x1 ... xn], normalised as the generator normalises them;
             a literal [true]/[false] is dropped *)
          let declared_atoms =
            lazy
              (match
                 PCSP.Params.candidate_atoms_at
                   (PCSP.Problem.params_of APCSP.problem)
                   tvar sorts
               with
              | None -> []
              | Some (xs, atoms) ->
                  let sub =
                    Map.Poly.of_alist_exn
                    @@ List.map2_exn xs (LogicOld.sort_env_list_of_sorts sorts)
                         ~f:(fun (x, _) (y, s) -> (x, LogicOld.Term.mk_var y s))
                  in
                  List.filter_map atoms ~f:(fun phi ->
                      let phi =
                        Normalizer.normalize @@ Evaluator.simplify
                        @@ LogicOld.Formula.subst sub phi
                      in
                      if LogicOld.Formula.(is_true phi || is_false phi) then None
                      else Some phi))
        end in
        if PCSP.Problem.is_bool_valued_ord_pred APCSP.problem tvar then
          match config.predicate_template with
          | DNF predicate_template ->
              (module Template.PredicateDNF.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort predicate_template
                        end)
                        (Arg) : Template.Function.Type)
          | Flex predicate_template ->
              (module Template.PredicateFlex.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort predicate_template
                        end)
                        (Arg) : Template.Function.Type)
          | Arrays predicate_template ->
              (module Template.PredicateArrays.Make
                        (struct
                          (* the path list is one contract between the
                             template and the example expansion, so the
                             sequence setting comes from here and not from the
                             template's own file *)
                          let config =
                            {
                              (ExtFile.unwrap_or_abort predicate_template) with
                              Template.PredicateArrays.Config.sequence_cells =
                                config.sequence_cells;
                              sequence_sentinel_cell =
                                config.sequence_cells
                                && config.sequence_sentinel_cell;
                            }
                        end)
                        (Arg) : Template.Function.Type)
        else if
          PCSP.Problem.(
            is_wf_pred APCSP.problem tvar || is_dwf_pred APCSP.problem tvar)
        then
          match config.wf_predicate_template with
          | WF wf_predicate_template ->
              (module Template.WFPredicate.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort wf_predicate_template
                        end)
                        (Arg) : Template.Function.Type)
          | WF_Flex wf_predicate_template ->
              (module Template.WFPredicateFlex.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort wf_predicate_template
                        end)
                        (Arg) : Template.Function.Type)
        else if PCSP.Problem.is_nwf_pred APCSP.problem tvar then
          match config.wf_predicate_template with
          | WF wf_predicate_template ->
              (module Template.NWFPredicate.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort wf_predicate_template
                        end)
                        (Arg) : Template.Function.Type)
          | WF_Flex _ ->
              failwith @@ sprintf "not supported: %s" (Ident.name_of_tvar tvar)
        else if PCSP.Problem.is_parity_pred APCSP.problem tvar then
          match config.wf_predicate_template with
          | WF wf_predicate_template ->
              (module Template.ParityPredicate.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort wf_predicate_template
                        end)
                        (Arg) : Template.Function.Type)
          | WF_Flex _ ->
              failwith @@ sprintf "not supported: %s" (Ident.name_of_tvar tvar)
        else if PCSP.Problem.is_fn_pred APCSP.problem tvar then
          match config.fn_predicate_template with
          | FN fn_predicate_template ->
              (module Template.FNPredicate.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort fn_predicate_template
                        end)
                        (Arg) : Template.Function.Type)
          | FN_Flex fn_predicate_template ->
              (module Template.FNPredicateFlex.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort fn_predicate_template
                        end)
                        (Arg) : Template.Function.Type)
        else if PCSP.Problem.is_tot_pred APCSP.problem tvar then
          let ne_config = ExtFile.unwrap_or_abort config.ne_predicate_template in
          let universal =
            Option.value_exn
              (Kind.tot_positions_of (PCSP.Problem.kind_of APCSP.problem tvar))
          in
          let functional relation =
            match config.fn_predicate_template with
            | FN fn_predicate_template ->
                (module Template.FNPredicate.MakeTot
                          (struct
                            let config =
                              ExtFile.unwrap_or_abort fn_predicate_template
                          end)
                          (Arg)
                          (struct
                            let universal = universal
                            let relation = relation
                          end) : Template.Function.Type)
            | FN_Flex _ ->
                failwith
                @@ sprintf
                     "not supported: a functional witness template for the \
                      total predicate %s needs the non-flexible functional \
                      predicate template"
                     (Ident.name_of_tvar tvar)
          in
          match ne_config.tot_witness_template with
          | Affine ->
              (module Template.NEPredicate.Make
                        (struct
                          let config = ne_config
                        end)
                        (Arg)
                        (struct
                          let universal = universal
                        end) : Template.Function.Type)
          | Functional -> functional false
          | Functional_or_relation -> functional true
        else if PCSP.Problem.is_adm_pred APCSP.problem tvar then
          (module Template.AdmPredicate.Make
                    (struct
                      let config =
                        ExtFile.unwrap_or_abort config.adm_predicate_template
                    end)
                    (Arg) : Template.Function.Type)
        else if PCSP.Problem.is_integ_pred APCSP.problem tvar then
          (module Template.IntegPredicate.Make
                    (struct
                      let config =
                        ExtFile.unwrap_or_abort config.integ_predicate_template
                    end)
                    (Arg) : Template.Function.Type)
        else if PCSP.Problem.is_int_fun APCSP.problem tvar then
          match config.int_function_template with
          | IntFun int_function_template ->
              (module Template.IntFunction.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort int_function_template
                        end)
                        (Arg) : Template.Function.Type)
          | IntFun_Flex int_function_template ->
              (module Template.IntFunctionFlex.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort int_function_template
                        end)
                        (Arg) : Template.Function.Type)
          (*else if PCSP.Problem.is_real_fun APCSP.problem tvar then
          match config.real_function_template with
          | RealFun real_function_template ->
              (module Template.RealFunction.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort real_function_template
                        end)
                        (Arg) : Template.Function.Type)
          | RealFun_Flex real_function_template ->
              (module Template.RealFunctionFlex.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort real_function_template
                        end)
                        (Arg) : Template.Function.Type)*)
        else if PCSP.Problem.is_regex APCSP.problem tvar then
          match config.regex_template with
          | RegEx regex_template ->
              (module Template.RegEx.Make
                        (struct
                          let config = ExtFile.unwrap_or_abort regex_template
                        end)
                        (Arg) : Template.Function.Type)
        else
          (* NOT "unsupported kind".  The chain above dispatches on the kind
             AND, in the ordinary-predicate arm, on the return sort being
             [bool]; an unknown of kind [Ord] returning anything else -- an
             SMT-LIB [declare-const] of a bit-vector or integer sort read as a
             constrained Horn problem -- falls through every arm and used to
             report its kind as the problem, which sends a reader to the kind
             table where everything is in order.  The sort is what no template
             covers, so say both.

             It is raised as its own exception rather than a [failwith] because
             it is an UNSUPPORTED INPUT and not an internal error: the caller
             turns it into [unknown], which is an ordinary answer, where a
             failure reaches the user as a backtrace and a sweep as a crash. *)
          raise
            (PCSP.Problem.NoTemplate
               (sprintf "no template for %s : %s of kind %s"
                  (Ident.name_of_tvar tvar)
                  (Term.str_of_sort @@ Logic.ExtTerm.to_old_sort
                  @@ Logic.Sort.ret_of data)
                  (Kind.str_of @@ PCSP.Problem.kind_of APCSP.problem tvar))))

  type qualifiers_map =
    ( Ident.tvar,
      (Ident.tvar * (Ident.tvar * (int * sort_env_list * Formula.t)) list) list
    )
    Map.Poly.t

  (* Print a qualifiers map in full -- every hole, every qualifier, every
     parameter with its sort.  Nothing calls it; it is the shape of that
     structure written down once, which is what makes it worth keeping. *)
  (* PORTED, UNCALLED. *)
  (* DUBIOUS as code -- it is a printer with no caller, kept only because it
     is the shape of a structure nothing else writes down. *)
  let _dump_qmap (qmap : qualifiers_map) =
    Map.Poly.iteri qmap ~f:(fun ~key ~data ->
        Debug.print @@ lazy (sprintf "key: %s" (Ident.name_of_tvar key));
        List.iter data ~f:(fun (hole, quals) ->
            Debug.print @@ lazy (sprintf " hole: %s" (Ident.name_of_tvar hole));
            List.iter quals ~f:(fun (param, (i, senv_list, phi)) ->
                Debug.print
                @@ lazy
                     (sprintf "  %s: row %d, %s" (Ident.name_of_tvar param) i
                        (Formula.str_of phi));
                List.iter senv_list ~f:(fun (tvar, sort) ->
                    Debug.print
                    @@ lazy
                         (sprintf "   %s : %s" (Ident.name_of_tvar tvar)
                            (Term.str_of_sort sort))))))

  (* [keep] selects the qualifiers the template of a hole is built from; the
     hole's parameters and arity are still read off the whole list, so a
     hole whose qualifiers are all dropped is the lambda of its own arity
     returning [true] (what its conjunction of dropped conjuncts simplifies
     to), never one built from [sorts] *)
  let hole_template_map_of ?(keep = Fn.id) hole_qualifiers_map sorts ~f =
    (* A hole with no qualifiers still has to be a lambda of the hole's own
       arity, and that is not always the atom's arity: a template may bind
       variables of its own -- a predicate quantified over an array index binds
       one per index -- and then every hole is applied to the atom's arguments
       *and* to those. Taking the arity from [sorts] there builds [\\ args. true]
       and applies it to more arguments than it binds, which surfaces far away
       as a boolean literal in head position ("unknown pred. symbol: (True)")
       during constraint generation.

       Every hole of one template is applied to the same parameters, so a hole
       that has no qualifiers can take its arity from a sibling that has some;
       [sorts] is the fallback for a template whose holes are all empty, which
       is the case this was written for. *)
    let senv_of_sibling =
      (* REACHABLE ON THE DEFAULT PATH, and [None] there. Only when the sibling
         is actually *longer* than the atom's arity, which no template produces
         unless it binds variables of its own, so a hole with no qualifiers
         still gets the lambda it got before and this costs no behaviour
         anywhere else. *)
      List.find_map hole_qualifiers_map ~f:(fun (_, quals) ->
          match quals with
          | (_, (_, qsenv, _)) :: _
            when List.length qsenv > List.length sorts ->
              Some (Logic.of_old_sort_env_list qsenv)
          | _ -> None)
    in
    Map.Poly.of_alist_exn
    @@ List.map hole_qualifiers_map ~f:(fun (hole, quals) ->
        ( hole,
          if List.is_empty quals then
            let senv =
              Option.value senv_of_sibling
                ~default:(Logic.sort_env_list_of_sorts sorts)
            in
            Logic.Term.mk_lambda senv @@ Logic.BoolTerm.mk_bool true
          else
            let senv =
              let _, (_, qsenv, _) = List.hd_exn quals in
              Logic.of_old_sort_env_list qsenv
            in
            f senv @@ Templ.gen_from_qualifiers (senv, keep quals) ))

  (* the certificate templates of the current templates, per predicate *)
  let ref_cert_templates :
      (Ident.tvar, Templ.kind_cert_templ list) Map.Poly.t ref =
    ref Map.Poly.empty
  (* several template sets coexist (the ucore variants); every generated
     certificate template is kept and the one whose parameters the model
     binds is used *)

  let candidate_of_model (temp_param_senv : Logic.sort_env_map)
      (templates : Logic.cand_map) (qualifiers_map : qualifiers_map)
      (model : Logic.model) : Logic.cand_map * (Ident.tvar * KindCert.t) list =
    (* The binding of each template parameter is looked up in a table built
       once from the model rather than by a scan of the model per parameter,
       which was quadratic: with one parameter per qualifier per hole and a
       model of the same size, a large vocabulary made this lookup the cost of
       the whole call.  [first_binding_table] keeps the first element of the
       model for each variable, which is exactly the element [List.find] on
       the variable returns, so the substitution is the same. *)
    let model_of_tvar = Logic.first_binding_table model in
    let temp_param_sub =
      Map.Poly.mapi temp_param_senv ~f:(fun ~key ~data ->
          snd (* ToDo: support parameteric candidate solution and CEGIS(T) *)
          @@ Logic.ExtTerm.remove_dontcare_elem
          @@
          match Hashtbl.find model_of_tvar key with
          | None -> ((key, data), None)
          | Some opt -> opt)
    in
    (* a qualifier whose parameter the model sets to 0 contributes only [true]
       to its hole's instantiated template, so it is left out before the
       template is built rather than simplified away after; the template is
       the same formula *)
    let drop_zero_keys =
      Templ.drop_zero_key_quals ~value_of:(Map.Poly.find temp_param_sub)
    in
    Map.Poly.mapi templates ~f:(fun ~key:tvar ~data:(sort, term) ->
        let hole_qualifiers_map = Map.Poly.find_exn qualifiers_map tvar in
        let hole_template_map =
          hole_template_map_of ~keep:drop_zero_keys hole_qualifiers_map
            (Logic.Sort.args_of sort)
            ~f:(fun senv ->
              Logic.ExtTerm.subst temp_param_sub
              >> Logic.ExtTerm.simplify_formula Map.Poly.empty
                   (Map.Poly.of_alist_exn senv))
        in
        if false then (
          Debug.print
          @@ lazy
               ("size before: " ^ string_of_int @@ Logic.ExtTerm.ast_size term);
          Debug.print @@ lazy (Logic.ExtTerm.str_of term));
        let term' = Logic.ExtTerm.subst temp_param_sub term in
        if false then (
          Debug.print
          @@ lazy ("size mid: " ^ string_of_int @@ Logic.ExtTerm.ast_size term');
          Debug.print @@ lazy (Logic.ExtTerm.str_of term'));
        let term' = Logic.ExtTerm.subst hole_template_map term' in
        let term' =
          if config.candidate_select_constant_cases then
            Common.PhaseTime.with_phase "select-cases" (fun () ->
                Logic.select_constant_cases term')
          else term'
        in
        if false then (
          Debug.print
          @@ lazy
               ("size after: " ^ string_of_int @@ Logic.ExtTerm.ast_size term');
          Debug.print @@ lazy (Logic.ExtTerm.str_of term'));
        assert (Set.is_empty @@ Logic.ExtTerm.fvs_of term');
        (sort, term'))
    |> fun cand ->
    (* the kind certificates, instantiated with the same parameter values and
       hole qualifiers as the predicates; an instantiation failure only loses
       the certificate *)
    let certs =
      List.filter_map (Map.Poly.to_alist templates) ~f:(fun (tvar, (sort, _)) ->
          let bound = Map.key_set temp_param_sub in
          let cert_params ct =
            ct.Templ.cert_params_shared @ ct.Templ.cert_params_x
            @ ct.Templ.cert_params_y
          in
          let xy ct = Set.Poly.of_list (List.map ~f:fst (cert_params ct)) in
          let tvs_of_pieces =
            List.concat_map ~f:(fun (disc, rs) ->
                Formula.tvs_of disc :: List.map rs ~f:Term.tvs_of)
          in
          let params_of ct =
            Set.diff
              (Set.Poly.union_list
                 (List.concat_map ct.Templ.cert_levels ~f:(fun (px, py) ->
                      tvs_of_pieces px @ tvs_of_pieces py)))
              (xy ct)
          in
          (* the certificate template must belong to the template set the
             model is for: its parameters are bound by the model and its
             qualifier holes are the current ones.  The parameters alone do
             not identify it — the NWF/Parity generators draw their ranking
             parameters from tables shared across regenerations, so a stale
             certificate template passes the parameter test with holes the
             current qualifier map does not have *)
          let hole_names =
            Set.Poly.of_list
              (List.map
                 (Map.Poly.find_exn qualifiers_map tvar)
                 ~f:(fst >> Ident.name_of_tvar))
          in
          let holes_of ct =
            Set.Poly.union_list
              (List.concat_map ct.Templ.cert_levels ~f:(fun (px, py) ->
                   List.map (px @ py) ~f:(fun (d, _) ->
                       Set.Poly.map (Formula.pvs_of d) ~f:Ident.name_of_pvar)))
          in
          match
            Option.bind (Map.Poly.find !ref_cert_templates tvar) ~f:(fun cts ->
                List.find cts ~f:(fun ct ->
                    (not (List.is_empty ct.Templ.cert_levels))
                    && Set.is_subset (params_of ct) ~of_:bound
                    && Set.is_subset (holes_of ct) ~of_:hole_names))
          with
          | None -> None
          | Some ct -> (
              try
                let hole_qualifiers_map =
                  Map.Poly.find_exn qualifiers_map tvar
                in
                let hole_template_map =
                  hole_template_map_of ~keep:drop_zero_keys hole_qualifiers_map
                    (Logic.Sort.args_of sort) ~f:(fun senv ->
                      Logic.ExtTerm.subst temp_param_sub
                      >> Logic.ExtTerm.simplify_formula Map.Poly.empty
                           (Map.Poly.of_alist_exn senv))
                in
                let uni =
                  Map.Poly.of_alist_exn
                    (Logic.of_old_sort_env_list (cert_params ct))
                in
                let inst t =
                  t
                  |> Logic.ExtTerm.subst temp_param_sub
                  |> Logic.ExtTerm.subst hole_template_map
                in
                let inst_f phi =
                  Evaluator.simplify
                  @@ Logic.ExtTerm.to_old_fml Map.Poly.empty uni
                  @@ inst (Logic.ExtTerm.of_old_formula phi)
                in
                let inst_t t =
                  Evaluator.simplify_term
                  @@ Logic.ExtTerm.to_old_trm Map.Poly.empty uni
                  @@ inst (Logic.ExtTerm.of_old_term t)
                in
                let inst_pieces =
                  List.map ~f:(fun (disc, rs) ->
                      (inst_f disc, List.map rs ~f:inst_t))
                in
                (* one ranking: the WF template is used for DWF too, so a DWF
                   solution's certificate is a union of one *)
                Some
                  ( tvar,
                    [
                      {
                        KindCert.params_shared = ct.Templ.cert_params_shared;
                        params_x = ct.Templ.cert_params_x;
                        params_y = ct.Templ.cert_params_y;
                        levels =
                          List.map ct.Templ.cert_levels ~f:(fun (px, py) ->
                              (inst_pieces px, inst_pieces py));
                        accepting = ct.Templ.cert_accepting;
                      };
                    ] )
              with e when not (Common.Timer.is_async e) ->
                Debug.print
                @@ lazy
                     (sprintf
                        "[kind certificate] instantiation of %s failed: %s"
                        (Ident.name_of_tvar tvar) (Exn.to_string e));
                None))
    in
    (cand, certs)

  let old_eval_qual polarity unknowns (_param_senv, cond, _sorts, args)
      (key, (_, params, phi)) =
    let fvs = Set.Poly.union_list @@ List.map ~f:LogicOld.Term.tvs_of args in
    let fenv = Map.Poly.empty in
    (*TODO: generate fenv*)
    if Set.are_disjoint fvs unknowns then (
      let phi =
        let sub =
          try
            Map.Poly.of_alist_exn @@ List.zip_exn (List.map ~f:fst params) args
          with exn_ when not (Common.Timer.is_async exn_) ->
            failwith
            @@ sprintf "old_eval_qual: %s -> %s"
                 (str_of_sort_env_list Term.str_of_sort params)
                 (List.to_string ~f:Term.str_of args)
        in
        Formula.subst sub phi
      in
      match Evaluator.check ~cond (Z3Smt.Z3interface.is_valid ~id fenv) phi with
      | Some true -> Logic.ExtTerm.(geq_of (mk_var key) (zero ()))
      | Some false -> Logic.ExtTerm.(leq_of (mk_var key) (zero ()))
      | None ->
          if false then
            Debug.print
            @@ lazy
                 (Formula.str_of phi
                ^ " couldn't be evaluated.  This may cause a violation of the \
                   progress property.");
          if not polarity then Logic.ExtTerm.mk_bool true
          else Logic.ExtTerm.(eq_of SInt (mk_var key) (zero ())))
    else (*never use*) Logic.ExtTerm.(eq_of SInt (mk_var key) (zero ()))

  let print_log = false

  (* With COAR_CGEN_PROFILE set, every [cgen] call prints one line to stderr:
     how many example clauses it converted, how many clauses the celled
     expansion made of them, and the wall time of each step of the conversion.
     A measurement instrument; without the variable nothing is timed. *)
  module CgenProfile = struct
    (* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
    let on = Lazy.from_val (match Sys.getenv "COAR_CGEN_PROFILE" with
      | None | Some "" -> false | Some _ -> true)
    let names = [| "expand"; "parts"; "witness"; "assemble"; "convert"; "close";
                   "seqinst"; "string"; "row"; "holemap"; "tsubst"; "hsubst";
                   "shared" |]
    let times = Array.create ~len:(Array.length names) 0.
    let clauses = ref 0
    let celled = ref 0
    let memo_hits = ref 0
    let memo_misses = ref 0
    let reset () =
      Array.fill times ~pos:0 ~len:(Array.length times) 0.;
      PCSatCommon.SharedParams.profile_reset ();
      clauses := 0; celled := 0; memo_hits := 0; memo_misses := 0
    let time i f =
      if not (Lazy.force on) then f ()
      else
        let t0 = Common.Clock.now_float () in
        Exn.protect ~f
          ~finally:(fun () ->
            times.(i) <- times.(i)
              +. Time_float.Span.to_sec (Time_float.diff (Common.Clock.now_float ()) t0))
    let report ~incremental total =
      if Lazy.force on then
        Stdlib.prerr_endline
        @@ sprintf "[cgen-profile] incremental %b sample %d celled %d memo %d/%d total %.3f %s"
             incremental !clauses !celled !memo_hits (!memo_hits + !memo_misses) total
        @@ String.concat ~sep:" "
        @@ (fun l -> l @ [ "|"; PCSatCommon.SharedParams.profile_report () ])
        @@ Array.to_list
        @@ Array.mapi names ~f:(fun i n -> sprintf "%s %.3f" n times.(i))
  end

  (* A census of one constraint's sharing, printed when the environment
     variable COAR_STEP_EXACT_CENSUS is set and otherwise never computed.  It
     interns every subterm and subformula bottom-up by its constructor and the
     ids of its children, so two equal subtrees get one id, and reports: the
     tree size, the number of distinct nodes (the size of the formula with each
     repeated subtree named once), and, for atoms and for [ite] terms, how many
     occurrences there are against how many distinct ones and the tree size
     those occurrences take.  A diagnostic instrument: it changes nothing. *)
  module SharingCensus = struct
    let on =
      Lazy.from_val
        (match Sys.getenv "COAR_STEP_EXACT_CENSUS" with
        | None | Some "" -> false
        | Some _ -> true)

    type entry = {
      mutable occ : int;
      size : int;
      kind : int;
      sample : string Lazy.t;
    }

    (* the same census over a higher-order term, before conversion: every
       node interned by its constructor and its children's ids *)
    let run_logic ~label (t : Logic.term) =
      let ids : (string, int) Hashtbl.t = Hashtbl.create (module String) in
      let occ : (int, int ref * int * string Lazy.t) Hashtbl.t =
        Hashtbl.create (module Int)
      in
      let node sample key size =
        let i =
          match Hashtbl.find ids key with
          | Some i -> i
          | None ->
              let i = Hashtbl.length ids in
              Hashtbl.set ids ~key ~data:i;
              Hashtbl.set occ ~key:i ~data:(ref 0, size, sample);
              i
        in
        let r, _, _ = Hashtbl.find_exn occ i in
        incr r;
        (i, size)
      in
      let rec go t =
        match t with
        | Logic.Var (x, _) -> node (lazy "") ("v" ^ Ident.name_of_tvar x) 1
        | Logic.Con (_, _) -> node (lazy "") ("c" ^ Logic.ExtTerm.str_of t) 1
        | Logic.App (a, b, _) ->
            let (ia, sa) = go a and (ib, sb) = go b in
            node (lazy (Logic.ExtTerm.str_of t)) (sprintf "a%d,%d" ia ib) (1 + sa + sb)
        | Logic.Bin (_, x, _, b, _) ->
            let ib, sb = go b in
            node (lazy (Logic.ExtTerm.str_of t))
              (sprintf "b%s.%d" (Ident.name_of_tvar x) ib) (1 + sb)
        | Logic.Let (x, _, d, b, _) ->
            let (id, sd) = go d and (ib, sb) = go b in
            node (lazy "") (sprintf "l%s,%d,%d" (Ident.name_of_tvar x) id ib) (1 + sd + sb)
        | Logic.TyApp (a, _, _) | Logic.TyLam (_, a, _) ->
            let ia, sa = go a in
            node (lazy "") (sprintf "t%d" ia) (1 + sa)
      in
      let _, size = go t in
      Stdlib.prerr_endline
      @@ sprintf "[step-exact-census] logic %s: tree %d dag %d" label size
           (Hashtbl.length ids);
      Hashtbl.data occ
      |> List.filter ~f:(fun (r, s, _) -> !r > 1 && s > 1)
      |> List.sort ~compare:(fun (r1, s1, _) (r2, s2, _) ->
             Int.compare ((!r2 - 1) * s2) ((!r1 - 1) * s1))
      |> (fun l -> List.take l 8)
      |> List.iter ~f:(fun (r, s, sample) ->
             let str = Lazy.force sample in
             Stdlib.prerr_endline
             @@ sprintf "[step-exact-census]   logic occ %d size %d: %s" !r s
                  (if String.length str > 400 then String.prefix str 400 ^ "..." else str))

    let run ~label (phi : Formula.t) =
      let ids : (string, int) Hashtbl.t = Hashtbl.create (module String) in
      let info : (int, entry) Hashtbl.t = Hashtbl.create (module Int) in
      let node ?(sample = lazy "") kind key size =
        let i =
          match Hashtbl.find ids key with
          | Some i -> i
          | None ->
              let i = Hashtbl.length ids in
              Hashtbl.set ids ~key ~data:i;
              Hashtbl.set info ~key:i ~data:{ occ = 0; size; kind; sample };
              i
        in
        let e = Hashtbl.find_exn info i in
        e.occ <- e.occ + 1;
        (i, size)
      in
      let ids_str l = String.concat ~sep:"," (List.map l ~f:(fst >> string_of_int)) in
      let sum l = List.fold l ~init:0 ~f:(fun acc (_, s) -> acc + s) in
      let rec term t =
        match t with
        | Term.Var (x, _, _) -> node 0 ("v" ^ Ident.name_of_tvar x) 1
        | Term.FunApp (sym, args, _) ->
            let cs = List.map args ~f:term in
            let kind = match sym with T_bool.IfThenElse -> 2 | _ -> 0 in
            node ~sample:(lazy (Term.str_of t)) kind
              (sprintf "f%s(%s)" (Term.str_of_funsym sym) (ids_str cs))
              (1 + sum cs)
        | Term.LetTerm (x, _, d, b, _) ->
            let cs = [ term d; term b ] in
            node 0 (sprintf "l%s(%s)" (Ident.name_of_tvar x) (ids_str cs)) (1 + sum cs)
      in
      let rec fml f =
        match f with
        | Formula.Atom (Atom.App (p, args, _), _) ->
            let cs = List.map args ~f:term in
            node ~sample:(lazy (Formula.str_of f)) 1
              (sprintf "a%s(%s)" (Predicate.str_of p) (ids_str cs)) (1 + sum cs)
        | Formula.Atom (a, _) -> node 1 ("a" ^ Atom.str_of a) 1
        | Formula.UnaryOp (op, g, _) ->
            let c = fml g in
            node 3 (sprintf "u%s(%d)" (Formula.str_of_unop op) (fst c)) (1 + snd c)
        | Formula.BinaryOp (op, g, h, _) ->
            let cs = [ fml g; fml h ] in
            node ~sample:(lazy (Formula.str_of f)) 3
              (sprintf "b%s(%s)" (Formula.str_of_binop op) (ids_str cs)) (1 + sum cs)
        | Formula.Bind (b, senv, g, _) ->
            let c = fml g in
            node 3
              (sprintf "q%s[%s](%d)" (Formula.str_of_binder b)
                 (String.concat ~sep:"," (List.map senv ~f:(fst >> Ident.name_of_tvar)))
                 (fst c))
              (1 + snd c)
        | Formula.LetFormula (x, _, d, g, _) ->
            let cs = [ term d; fml g ] in
            node 3 (sprintf "L%s(%s)" (Ident.name_of_tvar x) (ids_str cs)) (1 + sum cs)
        | Formula.LetRec _ -> node 3 (Formula.str_of f) 1
      in
      let _, size = fml phi in
      let stat kind =
        Hashtbl.fold info ~init:(0, 0, 0, 0, 0) ~f:(fun ~key:_ ~data:e (d, o, so, sd, mx) ->
            if e.kind = kind then (d + 1, o + e.occ, so + (e.occ * e.size), sd + e.size, max mx e.occ)
            else (d, o, so, sd, mx))
      in
      let pr name (d, o, so, sd, mx) =
        sprintf "%s distinct %d occurrences %d (max %d) tree-size %d distinct-size %d"
          name d o mx so sd
      in
      Stdlib.prerr_endline
      @@ sprintf "[step-exact-census] %s: tree %d dag %d | %s | %s" label size
           (Hashtbl.length ids) (pr "atoms" (stat 1)) (pr "ite" (stat 2))
      ;
      (* the subtrees whose repetition costs most, (occurrences - 1) * size *)
      Hashtbl.data info
      |> List.filter ~f:(fun e -> e.occ > 1 && e.size > 1)
      |> List.sort ~compare:(fun a b ->
             Int.compare ((b.occ - 1) * b.size) ((a.occ - 1) * a.size))
      |> (fun l -> List.take l 12)
      |> List.iter ~f:(fun e ->
             let str = Lazy.force e.sample in
             Stdlib.prerr_endline
             @@ sprintf "[step-exact-census]   kind %d occ %d size %d: %s" e.kind e.occ
                  e.size
                  (if String.length str > 300 then String.prefix str 300 ^ "..." else str))
  end


  (* Which row of the truth table an atom occupies -- the half of a qualifier
     evaluation that does not depend on the qualifier.  It used to be redone
     for every qualifier of every hole: 6.2 million normalizations,
     instantiations and lookups over 2,265 distinct atoms on twelve files in
     30 s each, 77 per constraint, of which four found an atom the table did
     not already hold.  Lazy because the two callers that need no row -- an
     atom with no qualifier, and the symbolic-hole branch below -- must not
     pay for it. *)
  let atom_row tt fenv qdeps unknowns atom =
    lazy
      (if Set.are_disjoint (ExAtom.tvs_of atom) unknowns then (
         if print_log then
           Debug.print
           @@ lazy (sprintf "[eval_qual] original: %s" (ExAtom.str_of atom));
         let atom = ExAtom.normalize_params atom in
         if print_log then
           Debug.print
           @@ lazy (sprintf "[eval_qual] normalized: %s" (ExAtom.str_of atom));
         let atom = ExAtom.instantiate atom in
         if print_log then
           Debug.print
           @@ lazy (sprintf "[eval_qual] instantiated: %s" (ExAtom.str_of atom));
         Some
           (CgenProfile.time 8 @@ fun () -> TruthTable.index_of_atom
              ~print:(if print_log then Debug.print ~id else fun _ -> ())
              ~id tt fenv qdeps atom))
       else None)

  (* Which truth table a predicate's rows live in.

     A truth table is a cache of "what is this qualifier's value at this
     example atom", so its rows and its columns have to agree about what an
     atom is.  When the candidate for an array-taking predicate may be
     [\ params. forall j. phi(j, a[j], params)], the qualifiers are over the
     parameters *extended* by the (index, value) columns, and they have no
     value at an atom that carries none -- an atom of the predicate's own
     arity.  So the extended rows need a table of their own, and the concrete
     one has to stay, because the labeler refutes from concrete atoms and the
     candidate shapes that quantify nothing are still in the search space.

     The two are distinguished by the key the table is looked up under, which
     costs no change of type: tables are created on demand per predicate.
     Nothing outside this module uses the extended key, so the labeler and the
     resolver go on seeing exactly the table they saw before. *)
  (* The arity is the DECLARED one, read off the problem: a celled example
     atom carries its cell columns among its own sorts, so its sort list is as
     long as the template's binders and would say "no cells". *)
  let template_has_cells template_map pvar =
    let tvar = Ident.pvar_to_tvar pvar in
    match
      ( Map.Poly.find template_map tvar,
        Map.Poly.find (PCSP.Problem.senv_of APCSP.problem) tvar )
    with
    | Some term, Some sort ->
        CellArray.has_cell_columns ~arity:(Logic.Sort.arity_of sort) term
    | _ -> false

  (* [celled]: whether the predicate's template took cell columns
     ([CellArray.table_key]). *)
  let table_of ~celled vs pvar =
    TruthTable.get_table vs.VersionSpace.truth_table
      (CellArray.table_key ~celled_examples:config.celled_examples ~celled pvar)

  let eval_qual (tt : TruthTable.table) row polarity (key, (qi, _params, phi)) =
    match Lazy.force row with
    | None -> (*never use*) Logic.ExtTerm.(eq_of SInt (mk_var key) (zero ()))
    | Some ai -> (
        if print_log then
          Debug.print @@ lazy (sprintf "[eval_qual] on %s" (Formula.str_of phi));
        match tt.cells.{qi, ai} with
        | 1 ->
            if print_log then Debug.print @@ lazy "[eval_qual] pos";
            Logic.ExtTerm.(geq_of (mk_var key) (zero ()))
        | -1 ->
            if print_log then Debug.print @@ lazy "[eval_qual] neg";
            Logic.ExtTerm.(leq_of (mk_var key) (zero ()))
        | _ ->
            if print_log then
              Debug.print
              @@ lazy
                   "[eval_qual] couldn't be evaluated.  This may cause a \
                    violation of the progress property.";
            if not polarity then Logic.ExtTerm.mk_bool true
            else Logic.ExtTerm.(eq_of SInt (mk_var key) (zero ())))

  let hole_map_of hole_qualifiers_map sorts ~f =
    (* Same arity rule as [hole_template_map_of]: a hole with no qualifiers is
       still a lambda of the *hole's* arity, which exceeds the atom's whenever
       the template binds variables of its own, so it is taken from a sibling
       hole when there is one. *)
    let senv_of_sibling =
      (* REACHABLE ON THE DEFAULT PATH, and [None] there -- see
         [hole_template_map_of]: longer than the atom's arity only *)
      List.find_map hole_qualifiers_map ~f:(fun (_, quals) ->
          match quals with
          | (_, (_, qsenv, _)) :: _
            when List.length qsenv > List.length sorts ->
              Some (Logic.of_old_sort_env_list qsenv)
          | _ -> None)
    in
    List.map hole_qualifiers_map ~f:(fun (hole, quals) ->
        ( hole,
          if List.is_empty quals then
            let senv =
              Option.value senv_of_sibling
                ~default:
                  (Logic.of_old_sort_env_list @@ sort_env_list_of_sorts sorts)
            in
            Logic.Term.mk_lambda senv @@ Logic.BoolTerm.mk_bool true
          else
            let senv =
              let _, (_, qsenv, _) = List.hd_exn quals in
              Logic.of_old_sort_env_list qsenv
            in
            Logic.Term.mk_lambda senv @@ Logic.BoolTerm.and_of
            @@ List.map ~f quals ))

  let cgen_from_fcon template_map qualifiers_map unknowns polarity
      (param_senv, phi) =
    Debug.print
    @@ lazy ("[cgen_from_fcon] generating hole map for: " ^ Formula.str_of phi);
    let hole_map =
      let hole_maps =
        List.concat_map ~f:(fun fvar_app ->
            let tvar, sargs, _, args, _ = Term.let_fvar_app fvar_app in
            (* NOT every application of a function variable is a template
               hole.  A function the INPUT defines -- an SMT-LIB
               [define-funs-rec], say -- is applied the same way and is an
               ordinary term with a definition of its own, so it has no
               qualifiers and no entry here, and asking for one raised
               [Not_found_s] out of the synthesizer: a backtrace where the user
               wanted an answer.

               Skipping it is not right either -- the template downstream still
               expects a hole for it, and leaves [hole0 is not bound] one step
               later -- so this is an input shape the synthesizer does not
               cover, and it says so in the one way the caller can turn into a
               verdict. *)
            match Map.Poly.find qualifiers_map tvar with
            | None ->
                raise
                  (PCSP.Problem.NoTemplate
                     (sprintf
                        "%s is applied as a function variable but is not one of \
                         the unknowns to synthesise"
                        (Ident.name_of_tvar tvar)))
            | Some hole_qualifiers_map ->
                hole_map_of hole_qualifiers_map sargs
                  ~f:
                    (old_eval_qual polarity unknowns
                       (param_senv, Formula.mk_true (), sargs, args)))
        @@ Set.to_list @@ Formula.fvar_apps_of phi
      in
      (* A NULLARY unknown never appears as an application here, so scanning
         the applications alone leaves its holes unbound and the run dies with
         "hole is not bound" after synthesis has already succeeded.  The
         higher-order representation the clause travels through has no
         application to zero arguments, so a nullary unknown written as one by
         a reader comes back from the round trip as an ordinary term variable:
         it is among the formula's variables and among the templates, and that
         is what identifies it.  Its hole is built exactly as an application's
         is, with no argument sorts and no arguments.

         [Formula.tvs_of] also returns the NAME of every applied function
         variable, so an applied unknown must be excluded here: counted a
         second time as a nullary one, its holes were bound twice and every
         function-synthesis query whose template had a hole died below with
         "multiple occurrences" on a single application. *)
      let applied_fvars =
        Set.Poly.map (Formula.fvar_apps_of phi) ~f:(fun app ->
            let tvar, _, _, _, _ = Term.let_fvar_app app in
            tvar)
      in
      let nullary_hole_maps =
        List.concat_map ~f:(fun tvar ->
            match Map.Poly.find qualifiers_map tvar with
            | None -> []
            | Some hole_qualifiers_map ->
                hole_map_of hole_qualifiers_map []
                  ~f:
                    (old_eval_qual polarity unknowns
                       (param_senv, Formula.mk_true (), [], [])))
        @@ Set.to_list
        @@ Set.filter (Formula.tvs_of phi) ~f:(fun tvar ->
            Map.Poly.mem template_map tvar && not (Set.mem applied_fvars tvar))
      in
      let hole_maps = hole_maps @ nullary_hole_maps in
      (* One function variable applied to two different argument lists in one
         example would need one copy of its holes per application, which this
         builder does not make: both copies share the hole names.  That is an
         input shape the synthesizer does not cover, so it is refused the way
         the case above is, as a verdict and not as a backtrace. *)
      match Map.Poly.of_alist hole_maps with
      | `Ok m -> m
      | `Duplicate_key hole ->
          raise
            (PCSP.Problem.NoTemplate
               (sprintf
                  "hole %s is bound twice: a function variable applied at \
                   several argument lists in one example is not supported"
                  (Ident.name_of_tvar hole)))
    in
    let term = Logic.ExtTerm.of_old_formula phi in
    if false then
      Debug.print
      @@ lazy ("size before: " ^ string_of_int @@ Logic.ExtTerm.ast_size term);
    let term' = Logic.ExtTerm.subst template_map term in
    if false then
      Debug.print
      @@ lazy ("size mid: " ^ string_of_int @@ Logic.ExtTerm.ast_size term');
    let term' = Logic.ExtTerm.subst hole_map term' in
    if false then
      Debug.print
      @@ lazy ("size after: " ^ string_of_int @@ Logic.ExtTerm.ast_size term');
    term'

  (* The cell index variables an exact step expansion ([celled_step_exact])
     made universal.  Constraint generation reads it twice: an atom holding one
     of them has its holes evaluated symbolically, since its truth-table row
     would put the index at a default; and no instantiation strategy grounds
     one, since the head demand is the universal and one instance of it is
     the weakening that let a candidate satisfy an example the validator then
     returned again.  Per module instance, like the rest of this module's
     state: one instance is driven by one synthesis loop.  Names are fresh, so
     a variable in it is never another's parameter. *)
  let exact_step_indices : Ident.tvar Hash_set.t = Hash_set.Poly.create ()

  let holds_exact_step_index atom =
    Map.Poly.existsi (ExAtom.params_of atom) ~f:(fun ~key ~data:_ ->
        Hash_set.mem exact_step_indices key)

  (* a parametric atom whose side condition has no satisfying parameter
     values denotes the empty set of examples; the literal it stands for is
     vacuously true, so the example clause imposes nothing (the truth table
     used to score every qualifier "true" there) *)
  let vacuous_cache : (string, bool) Hashtbl.t = Hashtbl.create (module String)

  let vacuous_atom vs atom =
    match ExAtom.to_old_atom_with_phi atom with
    | phi, _ when Formula.is_true phi -> false
    | phi, _ ->
        (* one Z3 call per distinct condition, not per constraint generation *)
        Hashtbl.find_or_add vacuous_cache (Formula.str_of phi)
          ~default:(fun () ->
            match
              try
                Ok
                  (Z3Smt.Z3interface.check_sat ~id vs.VersionSpace.fenv [ phi ])
              with e when not (Common.Timer.is_async e) -> Error e
            with
            | Ok `Unsat -> true
            | _ -> false)
        (* The handler lets a timeout through: catching it here swallowed the
           one-shot alarm of the caller's budget, so the whole check it was
           part of ran unbounded, and the answer "not vacuous" was cached for
           a query that was never decided. *)

  (* Extend a parametric atom's arguments with the index variables a
     quantified template binds, so that a hole's qualifier lambda can be
     applied to them.  This is the parametric-atom half of the array work:
     the cell route has none at all -- its [celled_example] refuses a
     [PPApp] -- and this is how the branch supplied one.

     It is kept uncalled because wiring it was tried twice and reverted, and
     the reason is a property of the query rather than of the plumbing: these
     variables arrive **free**, and a free variable in a synthesis query is
     existential -- the solver may pick one index -- where a quantified
     template means the disjunct holds for *every* index.  Binding them
     instead is what failed: in the hole's lambda they are never applied, and
     universally quantifying them inside the hole breaks the shared
     hole-map builder, whose parameter list means something else on the
     function-variable path.

     Note also that the names are global, so two predicates' templates
     conjoined in one query would identify their indices. *)
  (* PORTED, UNCALLED. *)
  (* DUBIOUS, and known to be: the variables it appends arrive FREE, which in
     a synthesis query is existential, where the quantified template means
     every index. Kept because it is the only parametric-atom story either
     branch has, not because it is right. *)
  let _extend_args_with_index_vars n args =
    args
    @ List.init n ~f:(fun i ->
          Term.mk_var (Ident.Tvar (sprintf "ivar%d" (i + 1))) T_int.SInt)

  (* The hole map substituted into an atom's instantiated template.  A hole
     has the predicate's arguments plus two columns per array cell as
     parameters (ten or more on the cell route), a body with one literal per
     qualifier, and a celled clause has dozens of atoms, each applying every
     hole.  Reducing those applications one argument at a time took three
     times as long as this, and was most of what constraint generation spent
     there before any solver call.  A hole whose qualifiers the truth table
     decided has a body over its selector variables only, and
     [Logic.Term.subst_up_to_bound_names] replaces its application by that
     body in one step; the result is [Logic.Term.subst]'s up to the names of
     bound variables (measured identical on 20,413 atom constraints of a
     celled run, whose templates bind nothing). *)
  (* the substitution of constraint generation other than the holes'; see
     [cgen_subst_rename_on_capture] *)
  let cgen_subst env term =
    if config.cgen_subst_rename_on_capture then
      Logic.Term.subst_rename_on_capture env term
    else Logic.Term.subst env term

  let subst_holes (holes : (Ident.tvar, Logic.term) Map.Poly.t) term =
    if config.hole_subst_rename_on_capture then
      Logic.Term.subst_up_to_bound_names_linear holes term
    else Logic.Term.subst_up_to_bound_names holes term

  (* The group names of [celled_step_exact_name_groups]
     ([PCSatCommon.HoleNaming]) for one [cgen] call, like the atom memo:
     [None] outside [cgen] and with the switch off.  [naming_clause] says
     whether the clause whose atoms are being built binds the names its atoms
     mention; an atom built outside such a clause is built without names, and
     the memo key keeps the two apart, so that a term holding a name never
     reaches a clause that does not bind it. *)
  let hole_naming : HoleNaming.table option ref = ref None
  let naming_clause = ref false

  (* Whether [pvar]'s template applies each of its holes only to its own
     lambda parameters, in their order, and has [arity] of them -- the
     precondition of [HoleNaming.hole_map]: then a hole's value at an atom is
     its body with the atom's arguments for its parameters.  A binder in the
     template body could shadow a parameter, so a body with one fails the
     test.  Per [cgen] call, since the templates change between calls. *)
  let template_shape_ok : (Ident.tvar, bool) Hashtbl.t = Hashtbl.Poly.create ()

  let holes_applied_to_params template_map hole_qualifiers_map pvar arity =
    let tvar = Ident.pvar_to_tvar pvar in
    Hashtbl.find_or_add template_shape_ok tvar ~default:(fun () ->
        match Map.Poly.find template_map tvar with
        | None -> false
        | Some template ->
            let params, body = Logic.Term.let_lam template in
            let params = List.map params ~f:fst in
            let holes = Set.Poly.of_list (List.map hole_qualifiers_map ~f:fst) in
            let rec ok t =
              match t with
              | Logic.Var (x, _) -> not (Set.mem holes x)
              | Logic.Con _ -> true
              | Logic.App _ -> (
                  let h, args = Logic.Term.let_apps t in
                  match h with
                  | Logic.Var (x, _) when Set.mem holes x -> (
                      match List.zip args params with
                      | Ok pairs ->
                          List.for_all pairs ~f:(function
                            | Logic.Var (y, _), x -> Stdlib.(x = y)
                            | _ -> false)
                      | Unequal_lengths -> false)
                  | _ -> ok h && List.for_all args ~f:ok)
              | Logic.Bin _ | Logic.Let _ | Logic.TyApp _ | Logic.TyLam _ ->
                  false
            in
            List.length params = arity && ok body)

  let cgen_from_ppapp ?(symbolic = false) vs template_map qualifiers_map
      unknowns polarity _param_senv _temp_param_senv atom =
    if vacuous_atom vs atom then Logic.BoolTerm.mk_bool true
    else
      let pvar, sorts =
        match (ExAtom.pvar_of atom, ExAtom.sorts_of atom) with
        | Some pvar, Some sorts -> (pvar, sorts)
        | _ -> failwith "cgen_from_ppapp"
      in
      let hole_qualifiers_map =
        Map.Poly.find_exn qualifiers_map (Ident.pvar_to_tvar pvar)
      in
      let tt =
        table_of ~celled:(template_has_cells template_map pvar) vs pvar
      in
      let fenv = vs.fenv in
      let qdeps = VersionSpace.qdeps_of pvar vs in
      if print_log then
        Debug.print @@ lazy "[cgen_from_ppapp] generating hole map";
      let hole_map =
        let symbolic_reading =
          (* Keeping the qualifier symbolic pays only where the *theory* is what
             leaves it undecided.  A parameter of a sort variable is such a case:
             the truth table has to pick a dummy element for it, and nothing says
             whether two dummies are equal, so a qualifier reading them is
             undecidable and gets dropped from the disjunct -- which removed the
             very qualifiers one invariant needed and made its synthesis query
             unsatisfiable at every template size.  A parameter of a fixed
             carrier (an integer, say) is not that case: its dummy is a concrete
             value, the qualifier is decided, and routing it through the solver
             only enlarges the query.  Measured: restricted to a sort variable
             this gains two answers over a corpus of quantified problems; applied
             to every parametric atom it also loses a three-line integer file
             that answers in under a minute without it. *)
          (* the sort-variable test is last on purpose: [&&] short-circuits, so
             a run with this route switched off pays nothing for it, and this
             test is made for every example atom *)
            (* an atom sharing a parameter with another atom of its clause,
               under [symbolic_shared_params]: its parameters are one variable
               across the clause, bound by the caller *)
            symbolic
            || config.symbolic_holes_for_parametric && ExAtom.is_ppapp atom
               && Map.Poly.exists (ExAtom.params_of atom) ~f:Sort.is_svar
            (* the exact celled head ([celled_head_exact]), recognised as a
               parametric head with an ARRAY parameter: on the cell route
               every other celled atom has its arrays grounded before its
               cells are read.  Its holes must see the cell indices, which
               the table's row would put at their defaults *)
            || config.celled_head_exact && polarity && ExAtom.is_ppapp atom
               && Map.Poly.exists (ExAtom.params_of atom) ~f:T_array.is_sarray
            (* an atom of an exact step expansion, on either side: its cell
               indices are the head's universal, and on the body side the
               frame instance reads the same variables *)
            || config.celled_step_exact && ExAtom.is_ppapp atom
               && holds_exact_step_index atom
        in
        let eval_hole =
          if symbolic_reading then
            (* route (a): keep the hole a constraint on the *selector*, as the
               decided cases do ([key >= 0] when the qualifier holds at the
               atom, [key <= 0] when it does not), but with the qualifier left
               symbolic instead of read off the truth table.  The hole's body
               says "this disjunct holds at these arguments": a qualifier with
               [key > 0] appears positively in the disjunct, one with [key < 0]
               negatively, so the general form is [key > 0 => q] and
               [key < 0 => not q], of which the decided cases are the instances
               ([q] true gives [key >= 0], [q] false gives [key <= 0]).
               [hole_map_of] binds the
               qualifier's parameters and the hole is applied to the atom's
               arguments, so [q] is evaluated there by the solver, together with
               the template parameters.  Substituting the qualifier's truth
               value for the hole instead (the first version of this branch)
               severs the link between the template and its selectors: every
               selector becomes unconstrained and the candidate degenerates to
               [true] — measured on cegis_loop_equality_sat.smt2, where the
               candidate was [P := true] in every one of 3 040 rounds. *)
            fun (key, (_qi, _params, phi)) -> SharedParams.route_a_hole key phi
          else eval_qual tt (atom_row tt fenv qdeps unknowns atom) polarity
        in
        (* the holes' group instances named once per [cgen] call, inside a
           clause that binds the names ([celled_step_exact_name_groups]) *)
        let named =
          match (!hole_naming, ExAtom.args_of atom) with
          | Some table, Some args
            when !naming_clause
                 && List.for_all args ~f:(fun t ->
                        Set.is_empty (Term.fvar_apps_of t))
                 && holes_applied_to_params template_map hole_qualifiers_map
                      pvar (List.length args) ->
              CgenProfile.time 9 @@ fun () ->
              HoleNaming.hole_map table
                ~prefix:
                  (sprintf "%s/%b/%b" (Ident.name_of_pvar pvar) polarity
                     symbolic_reading)
                ~subst:cgen_subst ~name_args:symbolic_reading args
                hole_qualifiers_map ~f:eval_hole
          | _ -> None
        in
        match named with
        | Some hole_map -> Map.Poly.of_alist_exn hole_map
        | None ->
        CgenProfile.time 9 @@ fun () ->
        Map.Poly.of_alist_exn
        @@ hole_map_of hole_qualifiers_map sorts ~f:eval_hole
        @
        match ExAtom.args_of atom with
        | None -> assert false
        | Some args ->
            List.concat_map ~f:(fun fvar_app ->
                let tvar, sargs, _, args, _ = Term.let_fvar_app fvar_app in
                let hole_qualifiers_map =
                  Map.Poly.find_exn qualifiers_map tvar
                in
                hole_map_of hole_qualifiers_map sargs
                  ~f:
                    (old_eval_qual polarity unknowns
                       (ExAtom.params_of atom, Formula.mk_true (), sargs, args)))
            @@ Set.to_list @@ Set.Poly.union_list
            @@ List.map ~f:Term.fvar_apps_of args
      in
      let _, term = ExAtom.to_formula polarity atom in
      if false then
        Debug.print
        @@ lazy ("size before: " ^ string_of_int @@ Logic.ExtTerm.ast_size term);
      let term' = CgenProfile.time 10 (fun () -> cgen_subst template_map term) in
      if false then
        Debug.print
        @@ lazy ("size mid: " ^ string_of_int @@ Logic.ExtTerm.ast_size term');
      let term' = CgenProfile.time 11 (fun () -> subst_holes hole_map term') in
      (*if print_log then
      Debug.print
      @@ lazy
           (sprintf "[cgen_from_ppapp] generated constr: %s"
              (LogicOld.Term.str_of
              @@ Logic.ExtTerm.to_old_trm Map.Poly.empty
                   (Map.force_merge param_senv temp_param_senv)
                   term'));*)
      if false then
        Debug.print
        @@ lazy ("size after: " ^ string_of_int @@ Logic.ExtTerm.ast_size term');
      term'

  (* One cgen's per-atom constraints, keyed by everything [cgen_from_ppapp]
     reads that varies within one call: whether the atom is read
     symbolically, its polarity, the atom, and the clause's unknowns.  The
     templates, the qualifiers and the version space are fixed for the call,
     and a truth-table row once added keeps its values, so a second call with
     the same key returns the same term.  On the cell route one example
     clause becomes one clause per head variant, each carrying the same
     celled body, so the same atoms recur: 15,247 of 35,660 atom constraints
     in one celled run were repeats.  [None] outside [cgen], so that nothing
     reads a memo built for other templates.  Keyed by structural
     comparison, which is exact because atoms are built in canonical shape (a
     non-canonical atom can only miss).  A hit skips the fresh names the
     computation would have drawn, which moves later names but not the
     constraint.

     An entry also holds the atom's share of the clause constraints it
     appears in ([DisjunctionAssembly.derived]), one per way of binding the
     clause's parameters, so that the conversion and simplification of the
     body a dozen head variants share is done once.  The share is a function
     of the term, the parameters and the grounding substitution, and of the
     template parameters' sorts, which are fixed for the call. *)
  type atom_entry = {
    term : Logic.term;
    mutable shares :
      (Logic.sort_env_list
      * (Ident.tvar * Logic.term) list option
      * DisjunctionAssembly.derived)
      list;
  }

  let atom_constr_memo :
      (bool * bool * bool * ExAtom.t * Ident.tvar list, atom_entry) Map.Poly.t
      ref
      option
      ref =
    ref None

  (* the guards of [celled_step_exact_name_groups]'s names as memo entries,
     one per name, for one [cgen] call *)
  let guard_entries : (Ident.tvar, atom_entry) Hashtbl.t = Hashtbl.Poly.create ()

  (* What [grow_keeping_disjuncts] buys on this side: an atom's constraint
     under a grown template computed from its constraint under the template
     it was grown from, by adding only the new disjuncts' share.

     Contract.  [compute ~full ~delta atom] returns a term equivalent to
     [full ()].  Where the atom's template [T] is registered in
     [TemplateLineage] as grown from [T_old] by [D] and this module holds the
     atom's term [c_old] under [T_old] for the same reading (symbolic or not,
     polarity, clause unknowns), it returns [c_old \/ c_D] for a positive atom
     and [c_old /\ c_D] for a negative one, where [c_D] is the atom's term
     under [D] alone with the qualifier map of [D]'s holes: the atom's term
     mentions the template once, positively in [P(t)] and under one negation in
     [not P(t)], each hole read the same way under either template, so
     [T = T_old \/ D] gives the two forms (a guard [c => .] or [c /\ .]
     around the occurrence distributes over both).  Otherwise it is
     [full ()].  Either way the result is remembered under [T], so the next
     growth step finds it.  The terms are functions of the atom, the reading
     and the template: the holes' qualifier lists are fixed per template and a
     truth-table row keeps its values once added.  Not used while hole naming
     is on, whose names are scoped to one [cgen] call. *)
  module GrownAtoms = struct
    let store :
        ( bool * bool * ExAtom.t * Ident.tvar list,
          (Logic.term * Logic.term) list )
        Map.Poly.t
        ref =
      ref Map.Poly.empty

    let find key tmpl =
      Option.bind (Map.Poly.find !store key) ~f:(fun l ->
          List.find_map l ~f:(fun (t, c) ->
              if phys_equal t tmpl then Some c else None))

    (* the two most recent templates per key: the current one and the one a
       next growth step starts from *)
    let remember key tmpl c =
      store :=
        Map.Poly.update !store key ~f:(fun l ->
            (tmpl, c)
            :: List.take
                 (List.filter (Option.value l ~default:[]) ~f:(fun (t, _) ->
                      not (phys_equal t tmpl)))
                 1)

    (* [COAR_GROWN_ATOM_CHECK] set: every reused term is also computed in
       full and the two are asked of Z3 for equivalence, counted as
       [synthesis/grown-atom/check-<outcome>]; a diagnostic, inert without it *)
    let checking =
      Lazy.from_val
        (match Sys.getenv "COAR_GROWN_ATOM_CHECK" with
        | None | Some "" -> false
        | Some _ -> true)

    let compute ?check ~symbolic ~polarity ~unknowns ~template_map
        ~qualifiers_map atom ~full ~delta =
      match (ExAtom.pvar_of atom, !hole_naming) with
      | Some pvar, None -> (
          let tvar = Ident.pvar_to_tvar pvar in
          match Map.Poly.find template_map tvar with
          | None -> full ()
          | Some tmpl ->
              let key = (symbolic, polarity, atom, Set.to_list unknowns) in
              let c =
                match TemplateLineage.find tmpl with
                | Some e -> (
                    match find key e.TemplateLineage.old with
                    | Some c_old ->
                        Common.PhaseTime.event "synthesis/grown-atom/reused";
                        let holes = e.TemplateLineage.delta_holes in
                        let qualifiers_map =
                          Map.Poly.update qualifiers_map tvar ~f:(function
                            | None -> []
                            | Some l ->
                                List.filter l ~f:(fun (h, _) ->
                                    List.mem holes h ~equal:Ident.tvar_equal))
                        in
                        let c_d =
                          delta
                            (Map.Poly.set template_map ~key:tvar
                               ~data:e.TemplateLineage.delta)
                            qualifiers_map
                        in
                        let c =
                          if polarity then Logic.BoolTerm.or_of [ c_old; c_d ]
                          else Logic.BoolTerm.and_of [ c_old; c_d ]
                        in
                        Option.iter check ~f:(fun check -> check c (full ()));
                        c
                    | None -> full ())
                | None -> full ()
              in
              if TemplateLineage.is_base tmpl then remember key tmpl c;
              c)
      | _ -> full ()
  end

  (* [cgen_from_exatom]'s term together with its memo entry, where there is
     one: an atom read through the truth table inside [cgen].  A formula atom,
     or any atom outside [cgen], has none. *)
  let cgen_from_exatom_entry ?symbolic vs template_map qualifiers_map unknowns
      param_senv temp_param_senv polarity = function
    | ExAtom.FCon (param_senv, phi) ->
        ( (if polarity then Fn.id else Logic.BoolTerm.neg_of)
          @@ cgen_from_fcon template_map qualifiers_map unknowns polarity
               (param_senv, phi),
          None )
    | ExAtom.(PApp ((_, _), _) | PPApp ((_, _), ((_, _), _))) as atom -> (
        let compute () =
          cgen_from_ppapp ?symbolic vs template_map qualifiers_map unknowns
            polarity param_senv temp_param_senv atom
        in
        let compute () =
          if not (TemplateLineage.active ()) then compute ()
          else
            let check =
              if not (Lazy.force GrownAtoms.checking) then None
              else
                Some
                  (fun c f ->
                    let senv = Map.force_merge param_senv temp_param_senv in
                    let old t = Logic.ExtTerm.to_old_fml Map.Poly.empty senv t in
                    let outcome =
                      try
                        match
                          Z3Smt.Z3interface.check_valid ~timeout:(Some 20000)
                            ~id vs.VersionSpace.fenv
                            (Formula.mk_iff (old c) (old f))
                        with
                        | `Valid -> "valid"
                        | `Invalid _ ->
                            Stdlib.Printf.eprintf
                              "[grown-atom-check] NOT EQUIVALENT\n%s\n%s\n%!"
                              (Formula.str_of (old c)) (Formula.str_of (old f));
                            "invalid"
                        | _ -> "undecided"
                      with e when not (Common.Timer.is_async e) -> "error"
                    in
                    Common.PhaseTime.event
                      ("synthesis/grown-atom/check-" ^ outcome))
            in
            GrownAtoms.compute ?check
              ~symbolic:(Option.value symbolic ~default:false)
              ~polarity ~unknowns ~template_map ~qualifiers_map atom
              ~full:compute ~delta:(fun template_map qualifiers_map ->
                cgen_from_ppapp ?symbolic vs template_map qualifiers_map
                  unknowns polarity param_senv temp_param_senv atom)
        in
        match !atom_constr_memo with
        | None -> (compute (), None)
        | Some memo -> (
            let key =
              ( Option.value symbolic ~default:false,
                !naming_clause,
                polarity,
                atom,
                Set.to_list unknowns )
            in
            match Map.Poly.find !memo key with
            | Some e -> incr CgenProfile.memo_hits; (e.term, Some e)
            | None ->
                incr CgenProfile.memo_misses;
                let e = { term = compute (); shares = [] } in
                memo := Map.Poly.set !memo ~key ~data:e;
                (e.term, Some e)))

  let cgen_from_exatom ?symbolic vs template_map qualifiers_map unknowns
      param_senv temp_param_senv polarity atom =
    fst
    @@ cgen_from_exatom_entry ?symbolic vs template_map qualifiers_map unknowns
         param_senv temp_param_senv polarity atom

  (* The entry's share for [params] and [sub], computed at the first request. *)
  let share_of_entry ~temp_param_senv ~params ~sub entry =
    let sub_key = Option.map sub ~f:Map.Poly.to_alist in
    match
      List.find entry.shares ~f:(fun (params', sub', _) ->
          Stdlib.(params' = params) && Stdlib.(sub' = sub_key))
    with
    | Some (_, _, d) -> d
    | None ->
        let d =
          DisjunctionAssembly.derive ~subst:cgen_subst ~temp_param_senv ~params
            ~sub entry.term
        in
        entry.shares <- (params, sub_key, d) :: entry.shares;
        d

  let _ = Random.init 0

  (* is [exists params. conds] satisfiable?  Cached: the same conditions recur
     across rounds.  A failure to decide counts as "do not assert". *)
  let witness_cache : (string, bool) Hashtbl.Poly.t = Hashtbl.Poly.create ()

  let witness_satisfiable fenv param_senv conds =
    match
      Formula.and_of
      @@ List.map conds ~f:(Logic.ExtTerm.to_old_fml Map.Poly.empty param_senv)
    with
    (* The CONVERSION can raise, and it used to do so outside the guard below,
       which covered only the solver call.  A condition may mention something
       that is not a parameter -- a NULLARY unknown is one, because it is a
       variable rather than an application and so appears in neither the
       parameter environment nor any argument list -- and the conversion then
       fails with that name unbound, out of the synthesizer, where the caller
       wanted a verdict.  It is a failure to decide like any other, so it takes
       the same answer: do not assert the witness.  That is the safe direction,
       since asserting it only ever WEAKENS what the candidate must satisfy. *)
    | exception exn_ when not (Common.Timer.is_async exn_) -> false
    | phi ->
    Hashtbl.Poly.find_or_add witness_cache (Formula.str_of phi)
      ~default:(fun () ->
        match Z3Smt.Z3interface.check_sat ~id fenv [ phi ] with
        | `Sat _ -> true
        | _ -> false
        | exception exn_ when not (Common.Timer.is_async exn_) -> false)

  (* ------------------------------------------------------------------
     The other route to a constraint from an example clause, preserved from
     the branch that wrote it: instead of evaluating each hole against the
     truth table, keep the clause's own quantifier structure and hand the
     result to a solver for quantified formulas.  A universal the example
     carries becomes a lambda, the whole is applied to a [QSAT] variable, and
     a clause that still has quantified variables is wrapped in one more
     universal -- the "QSAT hole" -- which is what a strategy-improvement
     solver is given to close.

     Switched by [qsat_clause_constraints], off by default.  It is unfinished
     on the branch and is kept because the *route* is a design alternative to
     the propositional abstraction and not merely an implementation of it: the
     hole stays a quantified formula rather than a row of a table.

     The polarity is not a defect, although it reads like one: both sides are
     built without a negation and the implication below supplies it, so the
     clause is [/\ negatives => \/ positives], which is what an example clause
     means.  What is genuinely open is *where the marker sits* relative to that
     negation: a negative atom currently yields [not (QSAT phi)], and whether
     the design wants [QSAT (not phi)] cannot be decided until the route runs.
     The vacuous boolean the marker binds makes the two the same formula and
     different queries, since only one of them hands the solver the negation. *)

  (* DEFERRED RATHER THAN ABANDONED.  The near-term goal for this template is
     the case where every index is universally quantified; letting a solver
     choose each quantifier's direction is the step after it.  The question
     that step has to answer before this is built: the argument that the
     abstraction loses nothing is made for a universally closed reading, and
     nothing is known about what an existential position does to it. *)
  (* UNREACHABLE BY DEFAULT (QSAT route). *)
  (* DUBIOUS in two ways, both of them the branch's and both preserved rather
     than repaired, because repairing unexercised code hides what it was. *)
  let replace_concrete_clause_with_QSAT vs template_map qualifiers_map unknowns
      temp_param_senv clause =
    let change_foralls_to_lambdas (term : Logic.term) =
      let open Logic in
      let rec iter (term : Logic.term) =
        match term with
        | Bin (Forall, tv, sort, rest, info) -> Bin (Lambda, tv, sort, iter rest, info)
        | _ -> term
      in
      iter term
    in
    let apply_qsat (term : Logic.term) =
      Logic.Term.mk_var_app (Ident.Tvar "QSAT") [ term ]
    in
    let prepend_qsat_hole (formula : Formula.t) =
      Formula.mk_bind Forall
        [ (Ident.Tvar "QSAT_HOLE", LogicOld.T_bool.SBool) ]
        formula
    in
    (* The QSAT term route, as far as it was taken: an example atom's constraint
       has its universals turned into lambdas and is handed to a single unknown
       [QSAT] applied to that abstraction, so that a solver for quantified
       formulas decides the whole atom instead of the truth table deciding each
       hole.  It is not wired to anything: on the branch this comes from, the
       only caller computed the term and discarded it.  Kept because the
       [QSAT_HOLE] binder below is the other half of the same design. *)
    let _qsat_term_of_exatom param_senv atom =
      apply_qsat @@ change_foralls_to_lambdas
      @@ cgen_from_exatom vs template_map qualifiers_map unknowns param_senv
           temp_param_senv true atom
    in
    let param_senv = Logic.of_old_sort_env_map @@ ExClause.params_of clause in
    (* No polarity parameter: both sides are built positively and
       [mk_imply] below negates the antecedent. *)
    let setup_formula atom =
      let term =
        cgen_from_exatom vs template_map qualifiers_map unknowns param_senv
          temp_param_senv true atom
      in
      let qvars =
        fst @@ Logic.Term.let_quants @@ snd @@ Logic.Term.let_lam term
      in
      let env_map, _ = ExAtom.to_old_formula true atom in
      let env_map = Map.Poly.map env_map ~f:Logic.ExtTerm.of_old_sort in
      let formula =
        Evaluator.simplify
        @@ Logic.ExtTerm.to_old_formula env_map temp_param_senv term []
      in
      let formula =
        if
          Set.exists (Formula.term_sort_env_of formula)
            ~f:(snd >> Term.is_string_sort)
          || Set.exists (Formula.funsyms_of formula) ~f:(function
               | T_string.StrConst _ -> true
               | _ -> false)
        then (* an ite is eliminated where the theory of strings is involved *)
          Evaluator.simplify @@ Formula.elim_ite formula
        else formula
      in
      let formula =
        if List.is_empty qvars then formula else prepend_qsat_hole formula
      in
      formula
    in
    let positives =
      Formula.or_of
      @@ List.map (Set.to_list clause.ExClause.positive) ~f:setup_formula
    in
    let negatives =
      Formula.and_of
      @@ List.map (Set.to_list clause.ExClause.negative) ~f:setup_formula
    in
    Formula.mk_imply negatives positives

  (* [cgen_from_pex]'s term, taken apart where [constr_of_pex] can assemble
     its conversion from shared per-atom pieces: [Disj] stands for

       with_witnesses (forall params (subst sub (or_of terms)))

     (no [subst] where [sub] is [None]), where [witness ()] decides the
     conjunct [with_witnesses] adds, and [entries] are the memo entries the
     terms came from.  [Whole] is every other shape. *)
  type pex_parts =
    | Whole of Logic.term
    | Disj of {
        params : Logic.sort_env_list;
        sub : (Ident.tvar, Logic.term) Map.Poly.t option;
        terms : Logic.term list;
        entries : atom_entry list;
        witness : unit -> Logic.term option;
      }

  let quantified_of_disj ~params ~sub terms =
    let phi = Logic.BoolTerm.or_of terms in
    Logic.BoolTerm.forall params
    @@ match sub with None -> phi | Some sub -> cgen_subst sub phi

  (* the term [cgen_from_pex] always returned; the quantified formula is built
     before the witness is decided, as it was *)
  let term_of_pex_parts = function
    | Whole t -> t
    | Disj { params; sub; terms; witness; _ } -> (
        let quantified = quantified_of_disj ~params ~sub terms in
        match witness () with
        | None -> quantified
        | Some w -> Logic.BoolTerm.and_of [ w; quantified ])

  let cgen_from_pex_parts vs template_map qualifiers_map unknowns
      temp_param_senv clause =
    let param_senv = Logic.of_old_sort_env_map @@ ExClause.params_of clause in
    let entries = ref [] in
    (* whether this clause binds the group names of its atoms' holes
       ([celled_step_exact_name_groups]); only the [Quantify] and
       [InstDefault] constraints below bind them.  The names enter only the
       terms [build_terms] builds: the shared-parameter reading builds its
       atoms itself, outside [naming_clause], so they hold no name *)
    let naming =
      config.celled_step_exact_name_groups && config.celled_step_exact
      && Option.is_some !hole_naming
      && (match config.pex_strategy with
         | Quantify | InstDefault -> true
         | InstRand _ -> false)
      && Set.exists
           (Set.union clause.ExClause.positive clause.ExClause.negative)
           ~f:holds_exact_step_index
    in
    let build_terms () =
      let f polarity atom =
        let t, entry =
          cgen_from_exatom_entry vs template_map qualifiers_map unknowns
            param_senv temp_param_senv polarity atom
        in
        Option.iter entry ~f:(fun e -> entries := e :: !entries);
        t
      in
      let outer = !naming_clause in
      naming_clause := naming;
      Exn.protect
        ~finally:(fun () -> naming_clause := outer)
        ~f:(fun () ->
          Set.to_list
          @@ Set.union
               (Set.Poly.map clause.ExClause.positive ~f:(f true))
               (Set.Poly.map clause.ExClause.negative ~f:(f false)))
    in
    (* Built at once, as it always was, unless [symbolic_shared_params] may
       replace it: building it registers the atoms' rows in the truth tables,
       which the shared-parameter reading of a symbolic atom must not do for
       nothing. *)
    let terms =
      if config.symbolic_shared_params then lazy (build_terms ())
      else Lazy.from_val (build_terms ())
    in
    let conds_of_clause () =
      Set.to_list
      @@ Set.Poly.filter_map ~f:Fn.id
      @@ Set.Poly.map
           (Set.union clause.ExClause.positive clause.ExClause.negative)
           ~f:(fun atom ->
             let _, cond, _ = ExAtom.to_old_formula_and_cond atom in
             if Formula.is_true cond then None
             else Some (Logic.ExtTerm.of_old_formula cond))
    in
    (* A parametric example's parameters are *witnesses* from a counterexample
       model, not universally quantified variables.  Both strategies bind them
       with [forall] -- [InstDefault] leaves the ones of a sort variable or an
       uninterpreted sort as variables and binds them at the end, exactly as
       [Quantify] does -- so the query says only [forall p. cond p => clause],
       which the solver can satisfy by shrinking an uninterpreted forall-sort to
       one element: there [cond] (typically [$1 <> $2]) is unsatisfiable and the
       example imposes nothing.  Checked directly: [(declare-sort a 0)] with
       [(assert (forall ((x a) (y a)) (=> (distinct x y) false)))] is [sat], and
       the candidate then stays [P := true] for ever.
       Conjoining [exists p. cond p] says that the example is required only of
       the types on which it is not empty, which is what the problem's semantics
       already says (a parametric example denotes every ground instance
       satisfying its condition; on a carrier with no such instance it denotes
       none).  Two guards: only a parameter of a **sort variable** counts — an
       integer's carrier is fixed, and including uninterpreted sorts ([SUS], the
       ADT/[declare-sort] case) cost `list_x_append_5.smt2` its answer
       (`unsat,3` in a second, then no answer in 120 s), the same trap that
       restricted [T_dt.mk_dummy_for] to sort variables — and the
       existential is asserted only when it is satisfiable -- a clause whose conditions cannot hold together is an
       empty example, and asserting them would make the synthesis query unsat
       (the clause-level counterpart of the vacuous parametric atom above). *)
    let witness () =
      if
        Map.Poly.for_all param_senv ~f:(function
          | Logic.Sort.SVar _ -> false
          | _ -> true)
      then None
      else
        match conds_of_clause () with
        | [] -> None
        | conds ->
            if witness_satisfiable vs.fenv param_senv conds then
              Some
                (Logic.BoolTerm.exists
                   (Map.Poly.to_alist param_senv)
                   (Logic.BoolTerm.and_of conds))
            else None
    in
    let with_witnesses quantified =
      match witness () with
      | None -> quantified
      | Some w -> Logic.BoolTerm.and_of [ w; quantified ]
    in
    (* The shared-parameter reading ([SharedParams.constraint_of]; its
       contract: the result implies the clause at every value of the shared
       parameters under the guard, is implied by the per-atom reading below,
       and quantifies no sequence).  A parameter outside the shared set is read
       exactly as the strategy below reads it.  [InstRand] is not covered: it
       conjoins several instances of the whole clause, and which of them a
       shared variable should range over is a question it does not answer. *)
    let shared =
      if not config.symbolic_shared_params then None
      else
        match config.pex_strategy with
        | InstRand _ -> None
        | (Quantify | InstDefault) as strategy -> (
            match
              try
                SharedParams.analyse
                  ~arity_of:(fun pvar ->
                    Option.map ~f:Logic.Sort.arity_of
                    @@ Map.Poly.find
                         (PCSP.Problem.senv_of APCSP.problem)
                         (Ident.pvar_to_tvar pvar))
                  clause
              with exn_ when not (Common.Timer.is_async exn_) -> None
            with
            | None -> None
            | Some analysis ->
                let ground key data =
                  match (strategy, data) with
                  | Quantify, _ -> None
                  | _, (Logic.DatatypeTerm.SUS _ | Logic.Sort.SVar _) -> None
                  | _, _ when Hash_set.mem exact_step_indices key -> None
                  | _, _ -> Some (Logic.ExtTerm.mk_dummy data)
                in
                (* a failure on the new path declines to the old one rather
                   than ending the run; a timeout is let through *)
                let result =
                  try
                    CgenProfile.time 12 @@ fun () ->
                    SharedParams.constraint_of ~subst:cgen_subst
                      ~temp_param_senv ~ground
                      ~atom_constr:(fun ~symbolic polarity atom ->
                        cgen_from_exatom ~symbolic vs template_map
                          qualifiers_map unknowns param_senv temp_param_senv
                          polarity atom)
                      analysis clause
                  with exn_ when not (Common.Timer.is_async exn_) -> None
                in
                Debug.print
                @@ lazy
                     (sprintf "[shared params] %s: %s"
                        (if Option.is_some result then
                           (* how many atoms the exact reading covers, which
                              is what bounds its cost; the clause printed
                              after it lists every atom *)
                           sprintf "exact, %d of %d atoms"
                             (Set.length analysis.SharedParams.symbolic)
                             (Set.length clause.ExClause.positive
                             + Set.length clause.ExClause.negative)
                         else "declined, per-atom reading kept")
                        (ExClause.str_of clause));
                result)
    in
    match shared with
    | Some constr -> Whole (with_witnesses constr)
    | None -> (
    let terms = Lazy.force terms in
    (* the names the terms mention, each bound by one more disjunct and one
       more universal ([HoleNaming]: the result is equivalent to the
       constraint with the hole bodies written out) *)
    let terms, name_params =
      match !hole_naming with
      | Some table when naming ->
          let guards = HoleNaming.guards table terms in
          (* a guard is a memo entry like an atom's, so that its share of the
             constraint is converted once per call however many clauses
             mention the name *)
          let gentries =
            List.map guards ~f:(fun ((n, _) as g) ->
                Hashtbl.find_or_add guard_entries n ~default:(fun () ->
                    { term = HoleNaming.guard g; shares = [] }))
          in
          entries := !entries @ gentries;
          ( terms @ List.map gentries ~f:(fun e -> e.term),
            List.map guards ~f:(fun (n, (sort, _)) -> (n, sort)) )
      | _ -> (terms, [])
    in
    if
      Lazy.force SharingCensus.on
      && Set.exists
           (Set.union clause.ExClause.positive clause.ExClause.negative)
           ~f:holds_exact_step_index
    then
      SharingCensus.run_logic
        ~label:(sprintf "terms (%d names)" (List.length name_params))
        (Logic.BoolTerm.or_of terms);
    let disj ~sub =
      Disj
        {
          params = Map.Poly.to_alist param_senv @ name_params;
          sub;
          terms;
          entries = !entries;
          witness;
        }
    in
    match config.pex_strategy with
    | Quantify -> disj ~sub:None
    | InstRand num ->
        let phi = Logic.BoolTerm.or_of terms in
        assert (num > 0);
        Whole
          (if Map.Poly.is_empty param_senv then phi
        else
          let open Ast.Logic in
          BoolTerm.forall (Map.Poly.to_alist param_senv)
          @@ BoolTerm.and_of
          @@ List.init num ~f:(fun k ->
              let sub =
                Map.Poly.mapi param_senv ~f:(fun ~key ~data ->
                    if Hash_set.mem exact_step_indices key then Term.mk_var key
                    else if k = 0 then ExtTerm.mk_dummy data
                    else
                      match data with
                      | IntTerm.SInt ->
                          ExtTerm.mk_int (Z.of_int @@ Integer.rand_int ())
                      | BoolTerm.SBool -> BoolTerm.mk_bool @@ Random.bool ()
                      | _ (*ToDo*) -> ExtTerm.mk_dummy data)
              in
              Term.subst sub phi))
    | InstDefault ->
        let sub =
          Map.Poly.mapi param_senv ~f:(fun ~key ~data ->
              match data with
              | Logic.DatatypeTerm.SUS _ | Logic.Sort.SVar _ ->
                  (* a parameter of an uninterpreted sort or of a sort variable
                     stays a variable, distinct from the others *)
                  Logic.Term.mk_var key
              (* so does a cell index of an exact step expansion: grounding it
                 would ask the head's universal at one index *)
              | _ when Hash_set.mem exact_step_indices key -> Logic.Term.mk_var key
              | _ -> Logic.ExtTerm.mk_dummy data)
        in
        disj ~sub:(if Map.Poly.is_empty sub then None else Some sub))

  (* An example clause's constraint as a term, whole.  UNCALLED: its one
     caller, [constr_of_pex_hinted], takes the parts apart to assemble the
     conversion; kept because it states what that conversion is of. *)
  let[@warning "-32"] cgen_from_pex vs template_map qualifiers_map unknowns
      temp_param_senv clause =
    term_of_pex_parts
    @@ cgen_from_pex_parts vs template_map qualifiers_map unknowns
         temp_param_senv clause

  (* An example clause's constraint as the synthesis query receives it:
     [cgen_from_pex]'s term, converted and simplified, with every ground term
     the theory leaves open bound universally ([SharedParams.close_open_terms],
     which states the soundness argument).  Such a term reaches the query
     wherever a qualifier is kept symbolic over an atom's arguments -- the
     sort-variable, exact-head, exact-step and shared-parameter readings --
     and one of those arguments is a literal or a parameter the default
     strategy grounded (an integer at [0], a sequence at the empty sequence, a
     datatype at its base constructor): a qualifier [nth x 0 = 7] at an empty
     sequence, [y mod x = 0] at [x = 0], [hd x >= 0] at [nil].  Left ground,
     its value is the solver's choice, so the query accepted a candidate that
     fails the example in some model.  The binding runs here, after the
     conversion and the simplification the query always had, because the term
     is not ground until the qualifier is applied to the atom's arguments and
     the result simplified.  It is the identity on a constraint with no such
     term, and draws no fresh name, so it changes nothing elsewhere.

     The second component is [true] only when the constraint provably
     mentions neither a variable of string sort nor a string constant (see
     [DisjunctionAssembly]); [false] says nothing.

     Where the clause's term is a disjunction of memoised atom terms under
     binders ([Disj]), the conversion and simplification are assembled from
     each atom's share ([DisjunctionAssembly.assemble]), which is the same
     formula; the shares are computed once per call and reused by every clause
     the atom occurs in.  When a witness conjunct is added, the witness is
     decided before the quantified formula is built rather than after, which
     can only move fresh names. *)
  let constr_of_pex_hinted vs template_map qualifiers_map unknowns
      temp_param_senv clause =
    let convert term =
      Evaluator.simplify
      @@ Logic.ExtTerm.to_old_fml Map.Poly.empty temp_param_senv term
    in
    let convert term = CgenProfile.time 4 (fun () -> convert term) in
    let phi, string_free =
      match
        CgenProfile.time 1 (fun () ->
          let parts = cgen_from_pex_parts vs template_map qualifiers_map unknowns
            temp_param_senv clause in
          (match parts with Disj { terms; _ } -> ignore (terms : Logic.term list) | _ -> ());
          parts)
      with
      | Disj { params; sub; terms; entries; witness }
        when DisjunctionAssembly.applicable terms -> (
          match CgenProfile.time 2 witness with
          | Some w ->
              ( convert
                @@ Logic.BoolTerm.and_of
                     [ w; quantified_of_disj ~params ~sub terms ],
                false )
          | None -> (
              match
                Option.all
                @@ List.map terms ~f:(fun t ->
                       List.find entries ~f:(fun e -> phys_equal e.term t))
              with
              | None -> (convert @@ quantified_of_disj ~params ~sub terms, false)
              | Some es ->
                  CgenProfile.time 3 (fun () ->
                  DisjunctionAssembly.assemble ~params
                  @@ List.map es
                       ~f:(share_of_entry ~temp_param_senv ~params ~sub))))
      | parts -> (convert @@ term_of_pex_parts parts, false)
    in
    let phi' = CgenProfile.time 5 (fun () -> SharedParams.close_open_terms ~temp_param_senv phi) in
    if not (phys_equal phi' phi) then
      Debug.print
      @@ lazy
           (sprintf "[open terms] bound in the constraint of %s"
              (ExClause.str_of clause));
    (phi', string_free && phys_equal phi' phi)

  let constr_of_pex vs template_map qualifiers_map unknowns temp_param_senv
      clause =
    fst
    @@ constr_of_pex_hinted vs template_map qualifiers_map unknowns
         temp_param_senv clause

  (* for SMT Solver *)

  let create_smt_instance ?(ucore = true) () =
    (* Qualifier searches and template rebuilds drop whole native contexts.
       Their native heaps do not drive OCaml's collector, so a fast failing
       search can exhaust the resident cap before those contexts are reclaimed.
       Collect before creating the next one once the resident set has grown
       enough for dropped contexts to matter: a collection before every one
       made forced collections a third to a half of a short run's wall clock.
       Live instances remain reachable. *)
    Z3Smt.Z3interface.full_major_if_resident_grew ();
    let ctx =
      Z3.mk_context
        (("model", "true") :: (if ucore then [ ("unsat_core", "true") ] else []))
      (*dummy*)
    in
    let solver =
      Z3.Solver.mk_solver ctx None
      (*dummy*)
    in
    let z3dtenv =
      Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx
      @@ PCSP.Problem.dtenv_of APCSP.problem
    in
    (* every defined function up front, or, under
       [declare_reached_functions_only], none: [declare_reached_in] then
       declares what each batch of formulas reaches before it is converted *)
    let z3fenv =
      Z3Smt.Z3interface.z3_fenv_of ~id ctx [] []
        (if Z3Smt.Z3interface.reached_functions_only () then Map.Poly.empty
         else LogicOld.get_fenv ())
        z3dtenv
    in
    let smt_timeout = config.smt_timeout in
    {
      ctx;
      solver;
      z3dtenv;
      z3fenv;
      smt_timeout;
      has_param_bounds = false;
      tracked_labels = ref [];
    }

  (* Declares in [inst]'s context the defined functions [phis] reach that it
     does not hold yet.  A no-op with [declare_reached_functions_only] off,
     since the instance then holds every function from its creation.  Must
     run before any of [phis] is converted into [inst]'s context: a function
     applied but not declared is converted as an uninterpreted symbol. *)
  let declare_reached_in (inst : smt_solver_instance) phis =
    if Z3Smt.Z3interface.reached_functions_only () then
      inst.z3fenv <-
        Z3Smt.Z3interface.declare_reached ~id inst.ctx inst.z3fenv
          (LogicOld.get_fenv ()) inst.z3dtenv phis

  let default_smt_instance = create_smt_instance ()

  let partial_sol_smt_instance =
    Map.Poly.map ~f:(fun _ -> create_smt_instance ())
    @@ PCSP.Problem.partial_sol_targets_of APCSP.problem

  let partial_sol_checking_smt_instance =
    Map.Poly.map ~f:(fun _ -> create_smt_instance ())
    @@ PCSP.Problem.partial_sol_targets_of APCSP.problem

  (* Does this solver still need the template-parameter bounds?  Answers once
     per solver and remembers, so the caller can write
     [~add_param_cnstrs:(take_param_cnstrs inst)] wherever it hands constraints
     to [csolve].  The instance is the right place to ask: the bounds constrain
     the parameters that solver's accumulated queries share, and a solver built
     fresh for one query needs them as much as the reused one does -- which the
     module counter this replaces could not express, since it is non-zero
     whenever the loop has iterated. *)
  let take_param_cnstrs instance =
    let needed = not instance.has_param_bounds in
    instance.has_param_bounds <- true;
    needed

  (* The unsat-core searches build a solver for one query and drop it, so it
     needs the template-parameter bounds every time -- which is exactly what the
     module counter could not say, being non-zero whenever the loop had
     iterated.  Naming the two together keeps them from drifting apart again. *)
  let fresh_ucore_instance ~ucore () = create_smt_instance ~ucore ()

  (* superseded by [has_param_bounds] on the instance itself; kept because the
     reset path still clears it and nothing else reads it *)
  let partial_sol_instances_with_bounds : Ident.tvar Hash_set.t =
    Hash_set.Poly.create ()

  (* Not a reset: this builds a whole new [Z3.mk_context] with its datatype and
     function environments, about 10 ms a time, and hands the fields over.  The
     cost is what a caller has to judge, which is why the name says "renew" --
     read as "reset", it made an optimisation look worth planning that is worth
     3.7 s over 51 benchmarks. *)
  let synthesis_timeout_cap =
    SynthesisBudget.cap_of ~configured:config.smt_timeout
      ~max_timeout:config.max_synthesis_timeout

  (* The budget the renewed instance starts with: the configured one, except
     that a rebuild caused only by a synthesis timeout keeps the instance's
     current (doubled, capped) budget when
     [keep_timeout_budget_across_rebuild] is on. *)
  let renew_smt_instance ~reason instance =
    (*Z3.Solver.reset instance.solver;*)
    let instance' = create_smt_instance () in
    instance.ctx <- instance'.ctx;
    instance.solver <- instance'.solver;
    instance.z3dtenv <- instance'.z3dtenv;
    instance.z3fenv <- instance'.z3fenv;
    instance.smt_timeout <-
      SynthesisBudget.on_rebuild
        ~keep:config.keep_timeout_budget_across_rebuild
        ~configured:instance'.smt_timeout ~cap:synthesis_timeout_cap
        ~current:instance.smt_timeout reason;
    instance.has_param_bounds <- instance'.has_param_bounds;
    instance.tracked_labels := []

  let renew_all_smt_instances ~reason () =
    renew_smt_instance ~reason default_smt_instance;
    Map.Poly.iter partial_sol_smt_instance ~f:(renew_smt_instance ~reason);
    Hash_set.clear partial_sol_instances_with_bounds

  (* Set just before a timeout-only failure recurses into a template rebuild,
     read and cleared by that rebuild; cleared at every [synthesize] call, whose
     examples may be new. *)
  let rebuild_after_timeout_only = ref false

  (* Whether the last [csolve] ended in a timeout -- Z3's, or the timer's
     raised through it -- rather than in [unknown] for another reason, which
     labels every predicate [TimeOut] too but does not raise the budget. *)
  let last_query_timed_out = ref false

  (* An answer that taught nothing but that the query ran out of time: no
     core, and every predicate labelled [TimeOut] alone. *)
  let timeout_only_labels ucores pvar_labels_map =
    Set.is_empty ucores
    && (not @@ Map.Poly.is_empty pvar_labels_map)
    && Map.Poly.for_all pvar_labels_map ~f:(fun labels ->
        Set.length labels = 1 && Set.mem labels TimeOut)

  (* for restart and templates/quals/terms update *)
  let iters_after_updated = ref 0
  let consecutive_failures = ref 0

  (* for unsat-core-based template update *)
  let ref_key_tvar_update_list_map = ref Map.Poly.empty

  (* for unsat-core-based qualifier learning *)
  let ref_key_clause_map = ref Map.Poly.empty

  (* for incremental solving *)
  let prev_sample = ref Set.Poly.empty
  let prev_cand = ref Map.Poly.empty

  (* whether [false_probe_on_negative_examples] has fired; it fires at most
     once per run, so a probe whose counterexamples add no positive example
     cannot be proposed again and again *)
  let false_probe_done = ref false

  let ref_templates =
    ref (Map.Poly.empty, Map.Poly.empty, Map.Poly.empty, Map.Poly.empty)

  (* Everything [initialize_templates] builds for one template shape: the
     template parameters, the template of each predicate, the constraints on
     those parameters, and, per predicate, the qualifiers behind each hole with
     the truth-table column each qualifier occupies. *)
  type shaped_templates =
    (Ident.tvar, Logic.Sort.t) Map.Poly.t
    * ( Ident.tvar,
        Logic.Sort.t * (parameter_update_type * Logic.term) )
      Map.Poly.t
    * ( Ident.tvar,
        (bool * parameter_update_type * Logic.term) Set.Poly.t )
      Map.Poly.t
    * ( Ident.tvar,
        (Ident.tvar * (Ident.tvar * (int * sort_env_list * Formula.t)) list)
        list )
      Map.Poly.t

  (* One way of learning a qualifier from an unsat core: a shape to give the
     qualifier template, and how to read the solution of that template back as
     qualifiers.  These are the second level of the failure policy described
     above [synthesize]; [templates] holds the templates of that shape, built
     once per hypothesis-space update by [initialize_templates].

     [shape] is one entry per disjunct, giving that disjunct's number of affine
     atoms, so [\[1\]] is a single atom and [\[2; 2\]] two disjuncts of two.
     [eq_atom] makes those atoms affine equalities instead of inequalities, and
     is [false] in every strategy below -- a degree of freedom this level has
     and does not use.  [only_bools] restricts the atoms to boolean qualifiers.
     [learn_whole_formula] takes the template's solution as one disjunctive
     qualifier instead of taking its atoms separately.  [ask_for_core] asks the
     SMT solver for an unsat core when this shape fails, which only the last
     strategy does, because only the last one's failure is reported upwards:
     the labeling map it returns is what the third level grows the templates
     from, and a solver that was not asked for a core returns an empty one, so
     the templates stop growing and the search makes no further progress
     (measured: eighteen of 123 CHC benchmarks stopped answering when all five
     were built alike).

     The order below is the escalation within this level, and it is not an
     order of increasing expressive power: reading a shape as the formulas it
     can state, [\[1\]] is below [\[1; 1\]] is below [\[2; 2\]], while the
     eight-disjunct shape is above [\[1; 1\]] and incomparable with [\[2; 2\]].
     So which order is right here is a question nobody has measured, the same
     question the second and third levels pose between them. *)
  type qualifier_learning_strategy = {
    name : string;
    shape : int list;
    eq_atom : bool;
    only_bools : bool;
    learn_whole_formula : bool;
    ask_for_core : bool;
    mutable templates : shaped_templates;
  }

  let no_templates () : shaped_templates =
    (Map.Poly.empty, Map.Poly.empty, Map.Poly.empty, Map.Poly.empty)

  (* The five strategies, tried in this order: a single atom first, then the
     boolean disjunction, then wider conjunctions, and last the one shape whose
     failure is allowed to reach the third level. *)
  let qualifier_learning_strategies =
    [
      {
        name = "ucore1";
        shape = [ 1 ];
        eq_atom = false;
        only_bools = false;
        learn_whole_formula = false;
        ask_for_core = false;
        templates = no_templates ();
      };
      {
        name = "ucore2";
        shape = [ 1; 1; 1; 1; 1; 1; 1; 1 ] (*ToDo*);
        eq_atom = false;
        only_bools = true;
        (* the disjunction of boolean qualifiers is learned whole: taking its
           atoms would give back the qualifiers it was built from.  This is
           meant, not a switched-off alternative, and it is a field here so
           that it is visible at the list. *)
        learn_whole_formula = true;
        ask_for_core = false;
        templates = no_templates ();
      };
      {
        name = "ucore3";
        shape = [ 1; 1 ] (*ToDo*);
        eq_atom = false;
        only_bools = false;
        learn_whole_formula = false;
        ask_for_core = false;
        templates = no_templates ();
      };
      {
        name = "ucore4";
        shape = [ 2; 2 ] (*ToDo*);
        eq_atom = false;
        only_bools = false;
        learn_whole_formula = false;
        ask_for_core = false;
        templates = no_templates ();
      };
      {
        name = "ucore5";
        shape = [ 1; 1; 1; 1; 1; 1; 1; 1 ] (*ToDo*);
        eq_atom = false;
        only_bools = false;
        learn_whole_formula = false;
        ask_for_core = true;
        templates = no_templates ();
      };
    ]

  let init_incr () =
    Debug.print @@ lazy "incremental SMT solver initialized";
    iters_after_updated := 0;
    ref_key_tvar_update_list_map := Map.Poly.empty;
    ref_key_clause_map := Map.Poly.empty;
    prev_sample := Set.Poly.empty;
    prev_cand := Map.Poly.empty
  (*
  let initialize () =
    (* for SMT Solver *)
    renew_all_smt_instances ();
    init_incr ();
    (* for incremental solving *)
    ref_templates := no_templates ();
    List.iter qualifier_learning_strategies ~f:(fun strategy ->
        strategy.templates <- no_templates ())
    *)

  (* let sel_env = ref Map.Poly.empty *)

  type lc = { label : string; constr : string } [@@deriving to_yojson]
  type ucores = string list [@@deriving to_yojson]

  (* ------------------------------------------------------------------
     Index/value cells for array-sorted arguments.

     A hypothesis space built over a predicate's own parameters can name an
     array [a] but not a read [a[i]], because a read needs an index and the
     parameter list has none.  These functions add the index and the value as
     extra *columns*: the template's parameter list is extended by [2 * qpa]
     integers per array-sorted parameter, and an example atom is extended by
     as many concrete integers, sampled from the contents of the array the
     example actually carries.  A qualifier over those columns then says
     "the array holds v at i", and [cell_to_array] reads the learned
     candidate back as a formula over [select a i], which is what the
     solution has to be.

     Ported from an abandoned branch; nothing calls it unless
     [celled_examples] is set. *)

  (* The current number of index/value pairs per array.  It is a global
     because the template that generates the extra parameters and the example
     expansion that fills them have to agree on the count, and they are
     reached from different phases. *)
  let current_qpa = ref 1

  (* The same count PER PREDICATE, which is what the read-back needs.  The
     global above is written by every atom the expansion touches, including one
     whose predicate reaches no array and therefore reports zero; the next
     read-back then computed its arity with a count of zero, removed no cell
     binders, and the candidate reached the conversion with the cell columns
     still on it, which fails far from here with "failed to convert term".  A
     shared mutable holding a per-object quantity is the shape this tree has
     paid for before. *)
  let cells_per_pred : (Ident.tvar, int) Hashtbl.Poly.t = Hashtbl.Poly.create ()

  (* How many times the example expansion has written [current_qpa], so that
     the expansion cache can replay the last write on a hit: the global is read
     back as a fallback by [cell_to_array], and a cache hit that skipped the
     write would leave it holding whatever an unrelated atom set last. *)
  let current_qpa_writes = ref 0

  (* the trie reader of an example's array, and the paths it is keyed on: a
     configuration-free module so that a test can reach it *)
  include CellArray

  (* The one list of cell paths every consumer below agrees on, sequences
     included exactly when the configuration asks for them. *)
  let array_paths_of_sorts sorts =
    CellArray.array_paths_of_sorts ~sequences:config.sequence_cells sorts

  (* whether a sequence's cells include the sentinel; the example side and the
     read-back both read this one value, so they cannot disagree *)
  let seq_sentinel = config.sequence_cells && config.sequence_sentinel_cell

  (* The CEGIS round the current synthesis call serves, set on entry to
     [synthesize]; read only by the growing range of a varying array. *)
  let current_round = ref 0

  (* An example atom split into the ground application the cell machinery
     works on and the wrapper that puts its parameters back, with those
     parameters' names.  An atom whose parameters survived instantiation is
     not refused on the ground that the cells read concrete arrays: the
     parameters that survive are exactly those of a quantified sort, so such a
     refusal would exclude every input whose array is a trait predicate over
     one.  A cell at a parameter is as concrete as the example is: the
     example means "for every instantiation of its parameters" and so does the
     celled one, which is why they are carried across rather than fixed. *)
  let split_atom (atom : ExAtom.t) :
      ExAtom.t * (ExAtom.t -> ExAtom.t) * Logic.sort_env_map =
    CellArray.split_example_atom
      ~keep_instance_guards:config.celled_keep_instance_guards atom

  (* The arrays an example atom carries, by argument position. *)
  let celled_example ~params (atom : ExAtom.t) =
    match atom with
    | ExAtom.PApp ((_, sorts), args) ->
        assert (List.length sorts = List.length args);
        (* The paths are already filtered to the arrays a cell can be built
           for -- integer-indexed, and holding something other than an array or
           a function -- so there is nothing to refuse here.  Refusing here is
           what an earlier version did, and it was wrong in a way worth
           remembering: an atom may carry a cellable array BESIDE one that is
           not, and one input does exactly that (a data array over a quantified
           sort, next to a trait predicate encoded as an array indexed by that
           sort).  A refusal is about the atom; the property is about one
           array. *)
        List.mapi (array_paths_of_sorts sorts) ~f:(fun k path ->
            ( k,
              eval_path ~sentinel:seq_sentinel ~params path @@ array_of_path path
              @@ List.nth_exn args path.CellQual.param ))
    (* a pure literal carries no arguments and so no arrays *)
    | _ -> []

  (* The indices worth offering at an INTEGER level, taken from the array
     itself: every index it stores, its two neighbours, and a small prefix.

     The neighbours are not arbitrary -- a region holding the array's default
     value is indistinguishable from the inside and distinguishable only at a
     boundary, so an offer set of stored indices alone can miss the very cell
     that refutes an example.

     This is the candidate set, and the exhaustive expansions consume it whole
     rather than sampling from it, which is what makes an example's demand the
     weakest sound reading on the body side and the strongest available one on
     the head side.  It is a fallback for the index the CLAUSE names: the index
     that makes an example false is known where the example is born, and an
     example atom records only the predicate's arguments, so it is lost.  An
     input whose witness index is outside this fixed set will still fail, and
     nothing here would say so. *)
  (* The candidate set is a guess, and this is where a wrong guess becomes
     visible: a refutation from an earlier round named an index, and either it is
     in the set just built or it is not.  A miss separates "the space could not
     say it" from "the space was never asked", which no verdict distinguishes and
     which an earlier measurement of this mechanism left open for exactly one
     index. *)
  let note_offer (cands : Z.t list) =
    match CellQual.note_offer cands with
    | [] -> ()
    | missed ->
        Debug.print
        @@ lazy
             (sprintf "[cell] refuting index not offered: %s"
                (String.concat ~sep:", " (List.map missed ~f:Z.to_string)))

  (* see [cell_candidates_below_zero] *)
  let below_zero_candidates () =
    List.init (max 0 config.cell_candidates_below_zero) ~f:(fun k ->
        Logic.IntTerm.mk_from_int (-(k + 1)))

  (* What the atom's own arguments contribute to the candidate indices, per
     level of the array: for an integer level the integers among the arguments
     with their neighbours, when [ints] asks for them; for any other level the
     terms of that sort the arguments reach, always, since there is no other
     source -- an invariant [forall b. q_p(cur x, b, v)] is the cell whose
     first and third indices are the argument terms [cur x] and [v]. *)
  let extra_candidates ~ints (atom : ExAtom.t) (path : CellQual.array_path) :
      Logic.term list list =
    match atom with
    | ExAtom.PApp ((_, sorts), terms) ->
        let args = List.zip_exn terms sorts in
        List.map path.CellQual.index_sorts ~f:(fun si ->
            if Term.is_int_sort si then
              (if not ints then []
              else
                List.concat_map terms ~f:(fun t ->
                    (* in [Z]: an argument is a model integer and may exceed a
                       native int *)
                    match LogicOld.T_int.let_int t with
                    | v -> List.map [ Z.pred v; v; Z.succ v ] ~f:Logic.IntTerm.mk_int
                    | exception exn_ when not (Common.Timer.is_async exn_) -> [])
                @
                if not config.cell_candidates_from_arg_sums then []
                else List.map (CellArray.argument_indices [ atom ]) ~f:Logic.IntTerm.mk_int)
              @ below_zero_candidates ()
            else
              List.map (CellQual.terms_of_sort si args) ~f:(fun t ->
                  Logic.ExtTerm.of_old_term @@ Evaluator.simplify_term t))
    | _ -> []

  (* The candidate cells of one array: an index tuple per combination of the
     per-level candidates, with the value the array holds there.

     An INTEGER level offers what it always did -- every stored index, its two
     neighbours, a short prefix, and the indices refutations have named -- plus
     whatever [extra] the caller collected from the atom.  A level of a sort
     that cannot be counted offers what the array stores at that level and the
     [extra] terms of that sort; nothing else can propose an index there.  A
     level with no candidate at all makes the array offer no cell, which the
     callers report and fall back from. *)
  let per_level_candidates ~(path : CellQual.array_path) ~extra ~from_array
      (array : cell_array) =
    level_candidates ~path ~extra ~from_array
      ~witnesses:
        (if not config.cell_witness_indices then []
         else
           (* the indices a refutation actually named, which is the one part
              of this set that is not a guess *)
           CellQual.witnesses ())
      array

  let make_cells ~(path : CellQual.array_path) ~(extra : Logic.term list list)
      ~from_array (array : cell_array) : (Logic.term list * Logic.term) list =
    let per_level = per_level_candidates ~path ~extra ~from_array array in
    (* the offer is noted where it is BUILT, which is the set the recorded
       measurement of this mechanism compared against; only an integer level
       has witnesses to compare against *)
    List.iter2_exn path.CellQual.index_sorts per_level ~f:(fun si cands ->
        if Term.is_int_sort si then
          note_offer
            (List.filter_map cands ~f:(function
              | Logic.Con (Logic.IntTerm.Int z, _) -> Some z
              | _ -> None)));
    cell_tuples ~path array per_level

  (* [extra_of k path] -- the caller's extra candidates for the [k]-th array of
     an atom -- with, when [cell_candidates_from_cell_values] is positive, the
     integer values the atom's OTHER arrays hold at the cells they offer added
     at every integer level (see that field).  The other arrays' cells are
     built from their own [extra_of] without this addition, so the values are
     one step deep, and without noting the offer, which is noted once where the
     array's own cells are built. *)
  let extra_with_cell_values ~from_array ~extra_of paths arrays k path =
    let extra = extra_of k path in
    let limit = config.cell_candidates_from_cell_values in
    if limit <= 0 then extra
    else
      let others =
        List.filter_mapi paths ~f:(fun k' path' ->
            if k' = k then None
            else
              let arr = Stdlib.List.assoc k' arrays in
              Some
                (cell_tuples ~path:path' arr
                   (per_level_candidates ~path:path' ~extra:(extra_of k' path')
                      ~from_array arr)))
      in
      add_at_int_levels ~path extra (int_values_of_cells ~limit others)

  (* [term_cell_key], [cell_key] and [dedup_cells] are [CellArray]'s, included
     above. *)

  (* NOT USED BY THE METHOD THIS TEMPLATE IS BEING BUILT FOR: it samples,
     and the method enumerates a set fixed by the clause.  The random source
     the cell sampling draws from.  It is this module's own, seeded by a constant, so that which cells
     a run offers is a function of the input alone: two runs of one binary on
     one file offer the same cells, while the several variants *within* a run
     still differ, which is what makes one clause worth more than one row.
     Drawing from the global [Random] instead made the choice depend on
     whatever else had drawn from it. *)
  let cell_random =
    (* COAR_CELL_SEED replaces the constant for a measurement: the seed is a
       coin the name-offset build family holds fixed, so a claim about one file
       under this route has to vary it too.  Unset, the constant stands. *)
    let seed =
      match Sys.getenv "COAR_CELL_SEED" with
      | Some s -> ( match Int.of_string_opt s with Some n -> n | None -> 20260921)
      | None -> 20260921
    in
    Random.State.make [| seed |]

  (* Which of the candidate cells to offer, where the shape does not admit
     taking them all: more than one array argument or more than one cell
     column, since the enumeration is then over tuples and the count is a
     product.  Without replacement: a repeated cell would spend two of the
     template's columns saying the same thing.  Fewer candidates than columns
     is not an error -- a short array has few indices worth offering -- so it
     offers what there is.

     Where it is reached, its weaknesses are the ones the exhaustive path
     exists to avoid: a sampled body atom demands falsity at a cell the example
     never claimed one, and a sampled head atom constrains a candidate at one
     cell out of several. *)
  (* How many times the sampler has drawn.  The expansion cache compares it
     before and after an expansion to tell a deterministic expansion, which it
     may reuse, from a sampled one, which it must not: reusing a sample would
     hand every later attempt the same draw where it would otherwise receive a
     fresh one, and skipping the draw would shift every draw after it. *)
  let cell_random_draws = ref 0

  let random_select qpa cells =
    let rec take n pool acc =
      if n <= 0 || List.is_empty pool then List.rev acc
      else
        let i =
          incr cell_random_draws;
          Random.State.int cell_random (List.length pool)
        in
        let chosen = List.nth_exn pool i in
        take (n - 1) (List.filteri pool ~f:(fun j _ -> j <> i)) (chosen :: acc)
    in
    take qpa (dedup_cells cells) []

  (* Exactly [qpa] cells from the ones sampled, for an atom whose sort list
     has already been widened by [qpa] cell columns: the atom's terms must
     fill every column, or the next array of the same atom is expanded from
     an atom whose terms and sorts disagree and every consumer that pairs
     them positionally breaks.  Fewer cells than columns is ordinary -- a
     short array has few indices worth offering, and an array over a sort
     that cannot be counted offers none at all when nothing is stored at
     some level and the atom's arguments reach no term of that sort (a
     constant array indexed by a quantified sort is such a one).

     Offered cells are repeated in order, which states nothing new: every one
     is a true index and value of the array.  With none offered, one cell is
     made: at each level its first candidate, and at a level with no
     candidate the plain constant of the level's sort, whose value is exact
     whatever that constant denotes because no node at that level stores
     anything.  A sequence is the exception, since a position outside its
     length reads a value the theory leaves open; it takes the sentinel cell,
     whose index is negative and whose value never reads the sequence, so no
     open term enters an example. *)
  let fill_cells qpa ~(path : CellQual.array_path) (arr : cell_array)
      (cells : (Logic.term list * Logic.term) list) :
      (Logic.term list * Logic.term) list =
    if qpa <= 0 || List.length cells >= qpa then cells
    else
      let cells =
        if not (List.is_empty cells) then cells
        else if CellQual.is_sequence path then
          [
            ( [ Logic.IntTerm.mk_from_int seq_sentinel_index ],
              seq_sentinel_value path.CellQual.elem_sort );
          ]
        else
          let per_level =
            level_candidates ~path ~extra:[] ~from_array:true ~witnesses:[] arr
          in
          let idxs =
            List.map2_exn path.CellQual.index_sorts per_level ~f:(fun si -> function
              | c :: _ -> c
              | [] -> Logic.ExtTerm.of_old_term (Term.mk_dummy si))
          in
          [
            ( idxs,
              value_at ~index_sorts:path.CellQual.index_sorts
                ~elem_sort:path.CellQual.elem_sort (Node arr) idxs );
          ]
      in
      List.init qpa ~f:(fun i -> List.nth_exn cells (i % List.length cells))

  (* Append [qpa] cells -- each an index tuple and a value, sampled from the
     array at path position [idx] -- to the atom, and return the indices so
     that the qualifier generator can see them. *)
  let expand (atom : ExAtom.t) qpa idx ~(path : CellQual.array_path) arrays :
      ExAtom.t * Term.t list =
    match atom with
    | ExAtom.PApp ((pvar, sorts), terms) ->
        (* the columns take the ARRAY's sorts, matching what the template
           generates for this path *)
        let cell_sorts =
          path.CellQual.index_sorts @ [ path.CellQual.elem_sort ]
        in
        let new_sorts =
          sorts @ List.concat (List.init qpa ~f:(fun _ -> cell_sorts))
        in
        let arr = Stdlib.List.assoc idx arrays in
        let pairs =
          fill_cells qpa ~path arr
          @@ random_select qpa
          @@ make_cells ~path ~extra:(extra_candidates ~ints:false atom path)
               ~from_array:true arr
        in
        (* converted with the example's parameters in scope: a cell's index or
           value may be one of them *)
        let to_old = to_old_in arr in
        let idxs = List.concat_map pairs ~f:(fun (is, _) -> List.map is ~f:to_old) in
        let terms =
          terms
          @ List.concat_map pairs ~f:(fun (is, v) -> List.map (is @ [ v ]) ~f:to_old)
        in
        (ExAtom.PApp ((pvar, new_sorts), terms), idxs)
    | _ -> assert false

  (* Every candidate cell of the one array argument, as one atom each.  The
     caller puts them on the body side of a single clause, where they read as a
     disjunction.  [None] where the shape does not admit the enumeration -- no
     array argument, more than one, or more than one cell column -- and the
     caller then samples as before. *)
  (* Per level of the [k]-th array path of [atom]: the forms through which the
     candidate space of [atom]'s predicate reads that level's index column, or
     [None] where it reads it some other way or the level is not constant --
     or, with [defaults], not a level [default_level] admits -- the [forms]
     argument of [collapse_constant_levels] and [collapse_default_levels];
     beside it, per level, the value substituted for the value column when
     those forms were computed, which is the [values] argument of the
     latter.

     The space is the template in [template_map] together with the qualifiers
     of its holes in [qualifiers_map].  The index column is found by POSITION
     in the template's binder list -- the predicate's own parameters, then one
     group of cell columns per path in path order, each as wide as its path,
     one group since the exhaustive expansion requires one cell per array --
     and by NAME in the qualifiers, whose parameter lists are built over the
     same variables; a qualifier whose list does not contain the column is a
     disagreement between the two and refuses the level.  The predicate's
     parameters are replaced by the atom's arguments; the cell's value column
     is replaced by the value only when every cell of the array holds the same
     one, and otherwise left, so an atom reading it beside the index refuses. *)
  let collapse_forms ?(defaults = false) ~qualifiers_map ~template_map
      (atom : ExAtom.t) paths k (arr : cell_array)
      (cells : (Logic.term list * Logic.term) list) :
      (Z.t * Z.t) list option list * Logic.term option list =
    match atom with
    | ExAtom.PApp ((pvar, sorts), args) -> (
        let tvar = Ident.pvar_to_tvar pvar in
        let path = List.nth_exn paths k in
        let nlevels = List.length path.CellQual.index_sorts in
        let refuse =
          (List.init nlevels ~f:(fun _ -> None), List.init nlevels ~f:(fun _ -> None))
        in
        match
          (Map.Poly.find template_map tvar, Map.Poly.find qualifiers_map tvar)
        with
        | Some template, Some hole_quals ->
            let binders, body = Logic.Term.let_lam template in
            let nsorts = List.length sorts in
            let offset =
              nsorts
              + List.sum (module Int) (List.take paths k) ~f:CellQual.cell_width
            in
            if List.length binders < offset + nlevels + 1 then refuse
            else
              let binder n = fst (List.nth_exn binders n) in
              let holes = Set.Poly.of_list (List.map hole_quals ~f:fst) in
              let quals =
                List.concat_map hole_quals ~f:(fun (_, qs) ->
                    List.map qs ~f:(fun (_, (_, qsenv, phi)) -> (qsenv, phi)))
              in
              (* the one value every cell holds, if there is one *)
              let uniform =
                match List.dedup_and_sort cells ~compare:(fun (_, a) (_, b) ->
                          String.compare (term_key a) (term_key b)) with
                | [ (_, v) ] -> Some v
                | _ -> None
              in
              (* Per level, the value substituted for the value column when that
                 level's forms are computed: the uniform value where there is
                 one; otherwise, under [defaults], at a level that stores values
                 and is the last one, the default its non-stored cells all hold
                 -- the collapse then gives a class only to cells holding it. *)
              let value_of j =
                match uniform with
                | Some v -> Some v
                | None ->
                    if defaults && j = nlevels - 1 && not (constant_level arr j)
                    then default_value arr j
                    else None
              in
              let arg_subst =
                List.zip_exn (List.map (List.take binders nsorts) ~f:fst) args
              in
              let values = List.init nlevels ~f:value_of in
              ( List.init nlevels ~f:(fun j ->
                    let idx = binder (offset + j) in
                    let admitted =
                      constant_level arr j || (defaults && default_level arr j)
                    in
                    if not admitted then None
                    else if mentions_outside_holes ~holes ~x:idx body then None
                    else
                      let subst =
                        Map.Poly.of_alist_reduce ~f:(fun a _ -> a)
                        @@ (match List.nth_exn values j with
                           | Some v -> [ (binder (offset + nlevels), to_old_in arr v) ]
                           | None -> [])
                        @ arg_subst
                      in
                      Option.map ~f:List.concat @@ Option.all
                      @@ List.map quals ~f:(fun (qsenv, phi) ->
                             if
                               not
                                 (List.exists qsenv ~f:(fun (x, _) ->
                                      Stdlib.( = ) x idx))
                             then None
                             else index_forms ~idx ~subst phi)),
                values )
        | _ -> refuse)
    | _ -> ([], [])

  (* The number of parameters a template abstracts over: its LEADING lambda
     binders, which are the predicate's own arguments followed by the cell
     columns.  Not every binder of the term -- a template that quantifies
     inside its body (quantifiers per array) has [forall] binders under the
     lambdas, and counting those as parameters took them for cell columns and
     built a sort the celled atoms disagree with. *)
  let lambda_params_of term = List.length (fst (Logic.Term.let_lam term))

  (* The celled atoms of [atom], one per tuple: [tuple] is one cell per path,
     in the order [paths] gives, which is the order the template's cell columns
     are generated in -- so the columns' sorts are that path's -- and each cell's
     indices and value are appended to the atom's arguments. *)
  let celled_atoms_of_tuples (atom : ExAtom.t) paths arrays tuples =
    List.map tuples ~f:(fun tuple ->
        match atom with
        | ExAtom.PApp ((pvar, sorts), terms) ->
            let with_sorts = List.zip_exn paths tuple in
            ExAtom.PApp
              ( ( pvar,
                  sorts
                  @ List.concat_map with_sorts ~f:(fun (path, _) ->
                        path.CellQual.index_sorts @ [ path.CellQual.elem_sort ]) ),
                terms
                @ List.concat_mapi tuple ~f:(fun k (is, v) ->
                      List.map (is @ [ v ]) ~f:(to_old_in (Stdlib.List.assoc k arrays))) )
        | _ -> assert false)

  (* What [expand_all_outcome] made of an atom: its expanded atoms; or, where
     the product of the per-array candidates is over [celled_product_bound],
     those candidates (and the relatedness offsets the product would filter
     by) so that a caller can sweep them; or nothing, where the shape declines
     the expansion or an array offered no cell. *)
  type expansion_outcome =
    | Expanded of ExAtom.t list
    | Over_bound of {
        paths : CellQual.array_path list;
        per_array : (Logic.term list * Logic.term) list list;
        related : Z.t list option;
      }
    | Declined

  let expand_all_outcome ?(wide = true) ?(extra_indices = []) ?qualifiers_map
      (atom : ExAtom.t) arrays (template_map : (Ident.tvar, Logic.term) Map.Poly.t)
      : expansion_outcome =
    match atom with
    | ExAtom.PApp ((pvar, sorts), _) ->
        let paths = array_paths_of_sorts sorts in
        let qpa =
          let extras =
            lambda_params_of
              (Map.Poly.find_exn template_map (Ident.pvar_to_tvar pvar))
            - List.length sorts
          in
          let denom = CellQual.total_cell_width paths in
          if denom = 0 || extras % denom <> 0 then 0 else extras / denom
        in
        if List.is_empty paths || qpa <> 1 then (
          (* Reported, because the caller's fallback is SILENT and weaker: the
             atom keeps a sampled cell instead of every candidate one, which is
             exactly the approximation the exhaustive route exists to remove.
             Three experiments on the candidate set were run and reported no
             difference while this was declining on every atom of the inputs
             they were about. *)
          Debug.print
          @@ lazy
               (sprintf
                  "celled expansion declined: %s paths=%d qpa=%d (a zero count \
                   here is usually an ALREADY celled clause coming back through \
                   the unsat-core restart, where re-expanding is a no-op)"
                  (Ident.name_of_pvar pvar) (List.length paths) qpa);
          Declined)
        else
          (* The candidates of EVERY array together, as the product.  With one
             array this is the list it always was; with two it is the pairs,
             and that is the case the single-array restriction written here
             first was hiding: an invariant relating two arrays is refuted at a
             PAIR of indices, so an expansion that draws each array's cell
             independently has the witness only by luck.  Measured on a slice
             walk, whose witness pair is (0, 0): the drawn pairs were (5,2),
             (2,1), (3,2), (1,1), and the correct invariant was rejected by all
             of them.

             The product is bounded, because it is a product: past the cap the
             atom keeps the sampled path, which is weaker and sound. *)
          let per_array =
            let from_array = not (config.cell_candidates_from_args_only && wide) in
            let extra_of _ path =
              extra_candidates ~ints:(config.cell_candidates_from_args && wide) atom path
            in
            List.mapi paths ~f:(fun k path ->
                make_cells ~path
                  ~extra:
                    (CellArray.add_at_int_levels ~path
                       (extra_with_cell_values ~from_array ~extra_of paths arrays k path)
                       (List.map extra_indices ~f:Logic.IntTerm.mk_int))
                  ~from_array
                  (Stdlib.List.assoc k arrays))
          in
          let per_array =
            match qualifiers_map with
            | Some qualifiers_map
              when (config.celled_collapse_constant_indices
                   || config.celled_collapse_default_indices)
                   && not
                        (config.celled_tuples_related
                        && List.length per_array >= 2) ->
                List.mapi per_array ~f:(fun k cells ->
                    let arr = Stdlib.List.assoc k arrays in
                    let defaults = config.celled_collapse_default_indices in
                    let forms, values =
                      collapse_forms ~defaults ~qualifiers_map ~template_map atom
                        paths k arr cells
                    in
                    let collapsed =
                      if defaults then collapse_default_levels ~forms ~values arr cells
                      else collapse_constant_levels ~forms arr cells
                    in
                    Debug.print
                    @@ lazy
                         (sprintf
                            "celled collapse: array %d, %d cell(s) to %d (%s)" k
                            (List.length cells) (List.length collapsed)
                            (String.concat ~sep:","
                               (List.map forms ~f:(function
                                 | None -> "-"
                                 | Some fs -> Int.to_string (List.length fs)))));
                    collapsed)
            | _ -> per_array
          in
          let related =
            if (not config.celled_tuples_related) || List.length per_array < 2 then None
            else
              Some
                (Z.zero
                ::
                (match atom with
                | ExAtom.PApp (_, terms) ->
                    List.filter_map terms ~f:(fun t ->
                        match LogicOld.T_int.let_int t with
                        | v -> Some v
                        | exception exn_ when not (Common.Timer.is_async exn_) -> None)
                | _ -> []))
          in
          (match array_product ~bound:config.celled_product_bound ?related per_array with
          | Empty ->
              Debug.print @@ lazy "celled expansion declined: an array offered no cells";
              Declined
          | Over size ->
              Debug.print
              @@ lazy
                   (sprintf
                      "celled expansion declined: product %d over bound %d (%d \
                       arrays)"
                      size config.celled_product_bound (List.length per_array));
              Over_bound { paths; per_array; related }
          | Tuples tuples -> Expanded (celled_atoms_of_tuples atom paths arrays tuples))
    | _ -> Declined

  let expand_all ?wide ?extra_indices ?qualifiers_map atom arrays template_map :
      ExAtom.t list option =
    match expand_all_outcome ?wide ?extra_indices ?qualifiers_map atom arrays template_map with
    | Expanded atoms -> Some atoms
    | Over_bound _ | Declined -> None

  (* The cells the sampler [expand] would draw for [atom] with one cell column
     per array: per array, in path order, the same pool, the same
     [random_select] and the same [fill_cells], so the draws taken -- and the
     cells drawn -- are exactly those of [extend_with_cells] on that atom. *)
  let sampled_cells (atom : ExAtom.t) paths arrays : (Logic.term list * Logic.term) list =
    List.mapi paths ~f:(fun k path ->
        let arr = Stdlib.List.assoc k arrays in
        match
          fill_cells 1 ~path arr
          @@ random_select 1
          @@ make_cells ~path ~extra:(extra_candidates ~ints:false atom path)
               ~from_array:true arr
        with
        | cell :: _ -> cell
        | [] -> assert false (* [fill_cells 1] always offers one cell *))

  (* The sweep [celled_over_bound_sweep] offers a body atom whose product is
     over the bound: per variant, the sampled tuple and the tuples that vary
     one array at a time over its candidates ([CellArray.array_sweep]).

     Contract.  Body atoms are premises, so a set [T] of offered tuples
     constrains a candidate by the disjunction of [not phi(t)] over [t] in
     [T]; a larger set is a weaker constraint.  With [S] the sampled tuples
     the fallback would offer, [W] the sweep and [P] the product,
     [S <= W <= P]: the sampled tuple is in its sweep by construction, and
     every varied tuple has one array's cell from that array's candidates and
     the others from the sample, which lie among their candidates whenever
     the sampler's pool is inside the exhaustive one (the ordinary
     configuration; a candidate set narrowed by collapsing equivalent cells or
     by the atom's arguments alone can leave a sampled cell outside, and then
     the sweep holds tuples outside the product, each still a true cell tuple
     of the counterexample).  Hence the sweep's constraint is implied by the
     sample's and implies the product's: it admits every candidate the
     sampled fallback admits, and admits nothing the exhaustive expansion
     rejects.

     Bounded by [m * celled_product_bound] tuples for [m] arrays -- each array
     ranging alone at most as wide as the bound allows one atom -- since the
     sweep is linear in the candidates; past that, [None], and the caller
     samples as before.  The draws are taken first, so a declined sweep
     draws exactly what the sampler then draws again, as it does today. *)
  let sweep_atoms ~num (atom : ExAtom.t) arrays ~paths ~per_array ~related :
      ExAtom.t list option =
    let m = List.length per_array in
    let size = List.sum (module Int) per_array ~f:List.length - (m - 1) in
    if size > m * config.celled_product_bound then (
      Debug.print
      @@ lazy
           (sprintf "celled sweep declined: %d tuples over bound %d (%d arrays)" size
              (m * config.celled_product_bound) m);
      None)
    else
      let tuples =
        List.concat
        @@ List.init num ~f:(fun _ ->
               CellArray.array_sweep ?related
                 ~base:(sampled_cells atom paths arrays)
                 per_array)
      in
      let tuples =
        List.dedup_and_sort tuples ~compare:(fun a b ->
            List.compare compare_cell_key (List.map a ~f:cell_key)
              (List.map b ~f:cell_key))
      in
      Debug.print
      @@ lazy
           (sprintf "celled sweep: %s, %d tuple(s) for a product of %d (%d arrays: %s)"
              (ExAtom.str_of atom) (List.length tuples)
              (List.fold per_array ~init:1 ~f:(fun a l -> a * List.length l))
              m
              (String.concat ~sep:"x"
                 (List.map per_array ~f:(fun l -> Int.to_string (List.length l)))));
      Some (celled_atoms_of_tuples atom paths arrays tuples)

  (* How many cells per array the template of an atom's predicate took, read off
     the template's leading binders; 0 where the count does not divide. *)
  let cells_per_array_of template_map pvar sorts paths =
    let extras =
      lambda_params_of (Map.Poly.find_exn template_map (Ident.pvar_to_tvar pvar))
      - List.length sorts
    in
    let denom = CellQual.total_cell_width paths in
    if denom = 0 || extras % denom <> 0 then 0 else extras / denom

  (* A goal example's body atom at the cells its clause read ([celled_goal_at_reads]):
     the tuples [GoalReads.cells_at_reads] gives for the atom's records, with
     every other array at the cells the exhaustive expansion would offer it.
     Any set of cells gives a constraint that implies the example (see
     [GoalReads.cells_at_reads]), so this is sound whatever the records hold.
     [None] -- the caller keeps its ordinary expansion -- where the atom has no
     cellable array, its template took other than one cell per array, or the
     tuples are empty or past [celled_product_bound]. *)
  let expand_at_goal_reads (atom : ExAtom.t) arrays template_map
      (records : GoalReads.record list) : ExAtom.t list option =
    match atom with
    | ExAtom.PApp ((pvar, sorts), _) ->
        let paths = array_paths_of_sorts sorts in
        if List.is_empty paths || cells_per_array_of template_map pvar sorts paths <> 1
        then None
        else
          let default_cells k path =
            let from_array = not config.cell_candidates_from_args_only in
            let extra_of _ path =
              extra_candidates ~ints:config.cell_candidates_from_args atom path
            in
            make_cells ~path
              ~extra:(extra_with_cell_values ~from_array ~extra_of paths arrays k path)
              ~from_array
              (Stdlib.List.assoc k arrays)
          in
          (match
             GoalReads.cells_at_reads ~paths ~arrays ~default_cells
               ~bound:config.celled_product_bound records
           with
          | Tuples tuples ->
              Debug.print
              @@ lazy
                   (sprintf "celled goal at reads: %s, %d record(s), %d tuple(s)"
                      (ExAtom.str_of atom) (List.length records) (List.length tuples));
              Some (celled_atoms_of_tuples atom paths arrays tuples)
          | Over size ->
              Debug.print
              @@ lazy
                   (sprintf "celled goal at reads declined: %d tuples over bound %d" size
                      config.celled_product_bound);
              None
          | Empty -> None)
    | _ -> None

  (* A head atom's cells as parameters: append, per cellable array and per cell
     column, a fresh index variable [j] and the value the atom's own array holds
     at [j].  The result is a parametric example, which [cgen_from_pex] binds
     with [forall] under the [Quantify] strategy.  That is meant to say what
     the concretization says the example means, [forall j. P#(j, a[j], x..)],
     and does not: the holes are evaluated at the atom's truth-table row, where
     [j] is at its default, and [a] is the array the example was grounded at
     ([celled_head_exact] is the form that keeps both).  [None] where the
     atom has no cellable array or the template took no cell columns, and the
     caller then leaves the atom alone. *)
  let expand_parametric ~full (atom : ExAtom.t) arrays
      (template_map : (Ident.tvar, Logic.term) Map.Poly.t) : ExAtom.t option =
    match atom with
    | ExAtom.PApp ((pvar, sorts), orig_args)
      when not (List.is_empty (array_paths_of_sorts sorts)) ->
        let paths = array_paths_of_sorts sorts in
        let qpa =
          let extras =
            lambda_params_of
              (Map.Poly.find_exn template_map (Ident.pvar_to_tvar pvar))
            - List.length sorts
          in
          let denom = CellQual.total_cell_width paths in
          assert (extras mod denom = 0);
          extras / denom
        in
        if qpa <= 0 then None
        else
          let params = ref [] and extra_sorts = ref [] and extra_args = ref [] in
          let conds = ref [] in
          List.iteri paths ~f:(fun k path ->
              let ps, ss, args, cs =
                parametric_cells ~full ~path (Stdlib.List.assoc k arrays) ~qpa
              in
              params := !params @ ps;
              extra_sorts := !extra_sorts @ ss;
              extra_args := !extra_args @ args;
              conds := !conds @ cs);
          Some
            (ExAtom.mk_ppapp
               (Map.Poly.of_alist_exn !params, Formula.and_of !conds)
               pvar
               (sorts @ !extra_sorts)
               (orig_args @ !extra_args))
    | _ -> None

  (* The exact form of a parametric head atom ([celled_head_exact]): the
     atom's parameters stay variables, and per cellable array and per cell
     column a fresh index variable [j] and the read [t[j]] of the atom's own
     array argument [t] are appended; the index variables join the atom's
     parameters, with its guard unchanged.  [None] where the atom is not
     parametric, has no cellable array, its template took no cell column, or an
     array is a sequence -- the caller then keeps its other paths. *)
  let expand_exact (atom : ExAtom.t)
      (template_map : (Ident.tvar, Logic.term) Map.Poly.t) : ExAtom.t option =
    match atom with
    | ExAtom.PPApp ((senv, cond), ((pvar, sorts), orig_args))
      when not (List.is_empty (array_paths_of_sorts sorts)) -> (
        let paths = array_paths_of_sorts sorts in
        match Map.Poly.find template_map (Ident.pvar_to_tvar pvar) with
        | None -> None
        | Some template ->
            let extras = lambda_params_of template - List.length sorts in
            let denom = CellQual.total_cell_width paths in
            if extras <= 0 || extras mod denom <> 0 then None
            else
              let qpa = extras / denom in
              let cells =
                List.map paths ~f:(fun path ->
                    let arg = List.nth_exn orig_args path.CellQual.param in
                    (* an array the example itself quantifies over gets its
                       cell values as fresh universals, which keeps the
                       synthesis query free of a universal over an array sort;
                       exact for a vocabulary that reads arrays only through
                       cells, a strengthening otherwise *)
                    let fresh_values =
                      match arg with
                      | Term.Var (x, _, _) -> Map.Poly.mem senv x
                      | _ -> false
                    in
                    CellArray.exact_parametric_cells ~fresh_values ~path arg ~qpa)
              in
              if List.exists cells ~f:Option.is_none then None
              else
                let cells = List.filter_map cells ~f:Fn.id in
                let params =
                  List.fold cells ~init:senv ~f:(fun acc (vars, _, _, _) ->
                      List.fold vars ~init:acc ~f:(fun acc (j, s) ->
                          Map.Poly.set acc ~key:j ~data:s))
                in
                let cond =
                  Formula.and_of
                    (cond :: List.concat_map cells ~f:(fun (_, _, _, cs) -> cs))
                in
                Some
                  (ExAtom.mk_ppapp (params, cond) pvar
                     (sorts @ List.concat_map cells ~f:(fun (_, ss, _, _) -> ss))
                     (orig_args
                     @ List.concat_map cells ~f:(fun (_, _, a, _) -> a))))
    | _ -> None

  (* The exact form of a step example ([celled_step_exact]): one body atom and
     one head atom, each over a predicate whose template took cell columns.
     The head gets its cells at fresh index variables, registered in
     [exact_step_indices] so that constraint generation keeps them universal;
     the body becomes one atom per instance [CellArray.exact_step_cells]
     returns, those that mention a head index carrying it as a parameter.  The
     result is ONE clause, the body instances being premises of it together.
     Taken after [split_atom], so the arrays read are the ones the other
     expansions read.  [None] where the helper declines or the shape is any
     other; the caller then keeps the ordinary expansion. *)
  let expand_exact_step (clause : ExClause.t)
      (template_map : (Ident.tvar, Logic.term) Map.Poly.t) : ExClause.t option =
    let qpa_of pvar sorts paths =
      match Map.Poly.find template_map (Ident.pvar_to_tvar pvar) with
      | None -> 0
      | Some template ->
          let extras = lambda_params_of template - List.length sorts in
          let denom = CellQual.total_cell_width paths in
          if denom = 0 || extras <= 0 || extras mod denom <> 0 then 0
          else extras / denom
    in
    let cell_sorts paths qpa =
      List.concat_map paths ~f:(fun (path : CellQual.array_path) ->
          List.concat
          @@ List.init qpa ~f:(fun _ -> path.index_sorts @ [ path.elem_sort ]))
    in
    let with_params params = function
      | ExAtom.PApp ((pvar, sorts), args) ->
          ExAtom.mk_ppapp (params, Formula.mk_true ()) pvar sorts args
      | ExAtom.PPApp ((senv, cond), ((pvar, sorts), args)) ->
          ExAtom.mk_ppapp
            ( Map.Poly.fold params ~init:senv ~f:(fun ~key ~data acc ->
                  Map.Poly.set acc ~key ~data),
              cond )
            pvar sorts args
      | a -> a
    in
    match
      (Set.to_list clause.ExClause.negative, Set.to_list clause.ExClause.positive)
    with
    | [ body ], [ head ] -> (
        let core_b, wrap_b, params_b = split_atom body in
        let core_h, wrap_h, params_h = split_atom head in
        match (core_b, core_h) with
        | ExAtom.PApp ((pb, sb), args_b), ExAtom.PApp ((ph, sh), args_h) -> (
            let paths_b = array_paths_of_sorts sb
            and paths_h = array_paths_of_sorts sh in
            let qpa_b = qpa_of pb sb paths_b and qpa_h = qpa_of ph sh paths_h in
            if qpa_b <= 0 || qpa_h <= 0 then None
            else
              let arrays atom params paths =
                List.map2_exn paths
                  (List.map ~f:snd (celled_example ~params atom))
                  ~f:(fun path arr -> (path, arr))
              in
              match
                CellArray.exact_step_cells
                  ~body:(arrays core_b params_b paths_b)
                  ~qpa_body:qpa_b
                  ~head:(arrays core_h params_h paths_h)
                  ~qpa_head:qpa_h
                  ~literals:
                    (CellArray.argument_indices ~cap:Int.max_value
                       [ core_b; core_h ])
                  ~bound:config.celled_product_bound
              with
              | None ->
                  (* printed because the fallback is silent and a run that
                     never took the exact form has not tested it *)
                  Debug.print
                  @@ lazy
                       (sprintf "celled step (exact): declined, %s"
                          (ExClause.str_of clause));
                  None
              | Some (js, head_args, instances) ->
                  List.iter js ~f:(fun (j, _) -> Hash_set.add exact_step_indices j);
                  let jparams = Map.Poly.of_alist_exn js in
                  let jset = Set.Poly.of_list (List.map js ~f:fst) in
                  let head_atom =
                    with_params jparams
                    @@ wrap_h
                         (ExAtom.PApp
                            ((ph, sh @ cell_sorts paths_h qpa_h), args_h @ head_args))
                  in
                  let body_atoms =
                    List.map instances ~f:(fun appended ->
                        let atom =
                          wrap_b
                            (ExAtom.PApp
                               ((pb, sb @ cell_sorts paths_b qpa_b), args_b @ appended))
                        in
                        let mentioned =
                          Set.inter jset
                            (Set.Poly.map ~f:fst
                            @@ Set.Poly.union_list
                            @@ List.map appended ~f:Term.term_sort_env_of)
                        in
                        if Set.is_empty mentioned then atom
                        else
                          with_params
                            (Map.Poly.filter_keys jparams ~f:(Set.mem mentioned))
                            atom)
                  in
                  Debug.print
                  @@ lazy
                       (sprintf "celled step (exact): %d body instance(s), head %s"
                          (List.length body_atoms) (ExAtom.str_of head_atom));
                  Some
                    (ExClause.canon
                       {
                         positive = Set.Poly.singleton head_atom;
                         negative = Set.Poly.of_list body_atoms;
                       }))
        | _ -> None)
    | _ -> None

  let extend_with_cells (atom : ExAtom.t) arrays
      (template_map : (Ident.tvar, Logic.term) Map.Poly.t) :
      ExAtom.t * int * Term.t list =
    match atom with
    | ExAtom.PApp ((pvar, sorts), orig_args)
      when not (List.is_empty (array_paths_of_sorts sorts)) ->
        let paths = array_paths_of_sorts sorts in
        let qpa =
          let extras =
            lambda_params_of
              (Map.Poly.find_exn template_map (Ident.pvar_to_tvar pvar))
            - List.length sorts
          in
          let denom = CellQual.total_cell_width paths in
          assert (extras mod denom = 0);
          extras / denom
        in
        let new_atom = ref atom and args = ref orig_args in
        List.iteri paths ~f:(fun k path ->
            let atom, idxes = expand !new_atom qpa k ~path arrays in
            new_atom := atom;
            args := !args @ idxes);
        (!new_atom, qpa, !args)
    (* A predicate with no array argument has no cells and no columns in its
       template, so the arithmetic above has nothing to divide by: it is left
       alone rather than expanded. *)
    | ExAtom.PApp _ -> (atom, 0, [])
    (* likewise a pure literal, which carries no arguments at all *)
    | _ -> (atom, 0, [])

  (* Replace each cell variable of a learned candidate by the read it stands
     for, and drop the cell binders: the candidate is then a formula over
     [select a i] and has the predicate's original arity again. *)
  let cell_var_to_array term assoc array_args =
    let substmap =
      Map.Poly.of_alist_exn
      @@ List.map assoc ~f:(fun (array_i, idxs, tvar) ->
             let arr, (path : CellQual.array_path) =
               List.nth_exn array_args array_i
             in
             ( tvar,
               cell_read ~sentinel:seq_sentinel ~path arr
                 (List.map idxs ~f:Logic.Term.mk_var) ))
    in
    let is_value_binder arg =
      List.exists assoc ~f:(fun (_, _, a) -> Stdlib.(a = arg))
    in
    let is_index_binder arg =
      List.exists assoc ~f:(fun (_, is, _) -> List.mem is arg ~equal:Stdlib.( = ))
    in
    let rec inner t =
      match t with
      | Logic.Bin (Logic.Lambda, arg, sort, rest, info) ->
          if is_value_binder arg then
            (* the value column is what [substmap] replaces by the array read,
               so its binder goes away with it *)
            inner rest
          else if is_index_binder arg then
            (* The index column does NOT become an argument of the predicate:
               the predicate's signature is the one the problem declared.  An
               example was expanded into one row per sampled index and every
               row had to be fitted, so a candidate that fits them all is being
               asserted at each of those indices, and the statement it makes
               about the array is a universal one -- which is the whole point
               of learning over cells, [P(v..)] defined as
               [forall i. phi(v.., i, a[i])].

               Universal rather than existential is what the examples justify
               (each sampled row is a separate constraint, all of which the
               candidate must satisfy), and it is a *candidate* either way:
               the validator checks it against the real clauses, so a reading
               that is too strong costs an answer and never soundness. *)
            (* a sequence cell's index ranges over the sequence's positions
               only: the read at any other index is a value the theory leaves
               open, so the universal takes the range as its premise *)
            let owner =
              List.find_map assoc ~f:(fun (array_i, is, _) ->
                  if List.mem is arg ~equal:Stdlib.( = ) then
                    Some (List.nth_exn array_args array_i)
                  else None)
            in
            let guard =
              Option.bind owner ~f:(fun (arr, path) ->
                  cell_read_guard ~sentinel:seq_sentinel ~path arr
                    [ Logic.Term.mk_var arg ])
            in
            let body = inner rest in
            if
              config.readback_drops_unused_cells
              && not (Logic.Term.occurs_free arg body)
            then
              (* [body] is [inner rest] after the value column was replaced by
                 the read, so an index that no longer occurs is used neither
                 as an index nor through its cell's value: the universal is
                 vacuous and [forall j. guard j => body] is
                 [(exists j. guard j) => body] *)
              match
                Option.bind owner ~f:(fun (arr, path) ->
                    cell_read_guard_satisfiable ~sentinel:seq_sentinel ~path arr)
              with
              | None -> body
              | Some nonempty -> Logic.BoolTerm.imply_of nonempty body
            else
              Logic.Term.mk_bind Logic.Forall arg sort
                (match guard with
                | None -> body
                | Some g -> Logic.BoolTerm.imply_of g body)
          else Logic.Bin (Logic.Lambda, arg, sort, inner rest, info)
      | _ -> Logic.Term.subst substmap t
    in
    inner term

  (* The inverse of [extend_sort_with_sorts]: drop the [n] arguments it
     appended.  The candidate that comes back from [cell_var_to_array] has the
     predicate's own arity again -- the cells were columns of the hypothesis
     space, never arguments -- so the sort recorded beside it has to lose them
     too, or the next consumer reads an arity the term does not have. *)
  let drop_cells_from_sort (sort : Logic.Sort.t) n =
    let rec inner sort k =
      match sort with
      | Logic.Sort.SArrow (t, c) when k > 0 ->
          Logic.Sort.SArrow (t, { c with val_type = inner c.val_type (k - 1) })
      | Logic.Sort.SArrow (_, c) -> inner c.val_type 0 (* an appended cell *)
      | sort -> sort
    in
    let keep = Logic.Sort.arity_of sort - n in
    if n <= 0 || keep < 0 then sort else inner sort keep

  (* UNREACHABLE BY DEFAULT (cells). The last step of the mechanism: a
     candidate learned over cell columns is rewritten into one over reads of
     the array, and loses the cell binders, so it has the predicate's own
     arity again. *)
  let cell_to_array (cand : Logic.cand_map) : Logic.cand_map =
    Map.Poly.mapi cand ~f:(fun ~key:pred ~data:(sort, term) ->
        (* a predicate whose template took no cell columns is left exactly as
           the model gave it -- not even alpha-renamed by the substitution
           below *)
        let declared_arity =
          Option.value_map ~default:(Logic.Sort.arity_of sort)
            ~f:Logic.Sort.arity_of
          @@ Map.Poly.find (PCSP.Problem.senv_of APCSP.problem) pred
        in
        if not (CellArray.has_cell_columns ~arity:declared_arity term) then
          (sort, term)
        else
        let args = fst @@ Logic.Term.let_lam term in
        (* the paths are taken from the ORIGINAL arguments; the cell columns
           appended after them are integers and reach no array, so counting
           over all of them gives the same answer and is simpler to state *)
        let paths =
          array_paths_of_sorts
          @@ List.map args ~f:(snd >> Logic.ExtTerm.to_old_sort)
        in
        let width = CellQual.total_cell_width paths in
        let qpa =
          Option.value ~default:!current_qpa @@ Hashtbl.find cells_per_pred pred
        in
        let arity = Logic.Sort.arity_of sort - (qpa * width) in
        let array_args =
          List.map paths ~f:(fun path ->
              let x, xsort = List.nth_exn args path.CellQual.param in
              ( Logic.ExtTerm.of_old_term
                @@ CellQual.read_path path
                @@ LogicOld.Term.mk_var x (Logic.ExtTerm.to_old_sort xsort),
                path ))
        in
        (* the cells lie after the original arguments, path-major and then
           cell by cell, each of its path's width: its index binders and then
           its value binder *)
        let assoc =
          let offset = ref arity in
          List.concat_mapi paths ~f:(fun i path ->
              List.init qpa ~f:(fun _ ->
                  let base = !offset in
                  offset := base + CellQual.cell_width path;
                  let nidx = List.length path.CellQual.index_sorts in
                  ( i,
                    List.init nidx ~f:(fun k -> fst @@ List.nth_exn args (base + k)),
                    fst @@ List.nth_exn args (base + nidx) )))
        in
        ( drop_cells_from_sort sort (qpa * width),
          cell_var_to_array term assoc array_args ))

  (* Add arguments of the given sorts, in order, in front of a predicate's
     result sort. *)
  let extend_sort_with_sorts (sort : Logic.Sort.t) (sorts : Logic.Sort.t list) =
    let rec inner = function
      | Logic.Sort.SArrow (t, c) ->
          Logic.Sort.SArrow (t, { c with val_type = inner c.val_type })
      | sort ->
          List.fold (List.rev sorts) ~init:sort ~f:(fun acc s ->
              Logic.Sort.mk_arrow s acc)
    in
    inner sort

  (* The celled variants of one example clause.  Each atom's array-sorted
     arguments are given concrete (index, value) pairs drawn from the array
     that example actually carries, and the variants differ because the
     sampling is random -- one clause is worth several rows of the truth
     table once the columns are cells.

     The polarities are kept, and which side an atom is on decides how its
     cells may be used, because a celled predicate means [forall j. phi(j,
     a[j])] and the two sides quantify it in opposite directions.

     An atom in the body is an ASSUMPTION of that shape, so every sampled cell
     is available at once and they all go into one clause: more assumptions
     make the clause easier to satisfy, and each is implied by the universal,
     so this is sound.

     An atom in the head is a GOAL of that shape.  Asking for it at one sampled
     cell is only a necessary condition, which is why the variants are separate
     clauses -- their conjunction is the closest the samples come to the
     universal -- and why a candidate that meets them still has to survive
     validation.  On the body side the same separation would be a strengthening
     instead: [not (forall j. phi)] is implied by [not phi(k)] at any single
     [k], so demanding it at every sampled [k] can reject a solution the
     problem admits, which costs answers rather than soundness.  Collecting
     them as one clause's assumptions is the weaker and therefore right
     reading.

     An earlier prototype put every atom on the positive side, which turns
     [P(a) => false] into [=> P(a)]: the head is then satisfied by the
     candidate that is true everywhere, no counterexample can refute it, and
     the loop proposes [true] for as long as it is given. *)
  (* Ground an example clause's parametric arrays (and, under their own
     switch, sequences) at values that vary; [CellArray.ground_varying] holds
     the construction and the argument that the result is an instance. *)
  let ground_arrays_varying_at ~inst (clause : ExClause.t) : ExClause.t =
    let grounded =
      CellArray.ground_varying ~arrays:config.celled_varying_array_instances
        ~sequences:config.celled_varying_sequence_instances
        ~width:config.celled_varying_array_width
        ~at_args:config.celled_varying_array_at_args
        ~growing:config.celled_varying_array_growing ~round:!current_round ~inst
        clause
    in
    (* printed because nothing else in a run says whether any example had a
       parameter this could ground *)
    if not (phys_equal grounded clause) then
      Debug.print
      @@ lazy
           (sprintf "grounded parametric containers at varying values: %s"
              (ExClause.str_of grounded));
    grounded

  let head_witnesses_of_clause (clause : ExClause.t) : Z.t list =
    if not config.celled_head_at_witnesses then []
    else
      List.dedup_and_sort ~compare:Z.compare
      @@ List.concat_map (Set.to_list clause.ExClause.positive)
           ~f:GoalReads.head_witnesses_of_atom

  let celled_clauses_of_uncached ?qualifiers_map ~num template_map (clause : ExClause.t) :
      ExClause.t list =
    (* [celled_head_at_witnesses]: the indices the refutations behind this
       example named in its head, read with the example as it is stored --
       before any grounding below, which would change the key -- and offered to
       every head atom of every instance; with one head atom, the usual shape,
       that is the atom they were recorded for *)
    let head_witnesses = head_witnesses_of_clause clause in
    if not (List.is_empty head_witnesses) then
      Debug.print
      @@ lazy
           (sprintf "celled head at witnesses: %s"
              (String.concat_map_list ~sep:"," head_witnesses ~f:Z.to_string));
    (* the exact head: one parametric head atom and no body, so no parameter
       is shared with an atom grounded below, and the atom is taken before any
       grounding of its arrays *)
    let exact =
      if config.celled_head_exact && Set.is_empty clause.ExClause.negative then
        match Set.to_list clause.ExClause.positive with
        | [ atom ] ->
            Option.map (expand_exact atom template_map) ~f:(fun atom ->
                Debug.print
                @@ lazy (sprintf "celled head (exact): %s" (ExAtom.str_of atom));
                [
                  ExClause.canon
                    { positive = Set.Poly.singleton atom; negative = Set.Poly.empty };
                ])
        | _ -> None
      else None
    in
    match exact with
    | Some clauses -> clauses
    | None ->
    let instances =
      if
        not
          (config.celled_varying_array_instances
          || config.celled_varying_sequence_instances)
      then [ clause ]
      else
        List.map (List.init (max 1 config.celled_array_instances) ~f:Fn.id)
          ~f:(fun inst -> ground_arrays_varying_at ~inst clause)
    in
    List.concat_map instances ~f:(fun clause ->
    match
      if config.celled_step_exact then expand_exact_step clause template_map
      else None
    with
    | Some exact -> [ exact ]
    | None ->
    (* Each atom's arrays are read from THAT atom at the point it is expanded
       ([own_arrays]).  They used to be read once per side and concatenated,
       keyed by path position, so with two array-carrying atoms on one side the
       second atom's cells were drawn from the first atom's array -- the
       candidate indices, the appended values and a parametric expansion's
       guard all describing an array the atom does not hold.  No tracked input
       has that shape, which is why it went unseen. *)
    let own_arrays core params = celled_example ~params core in
    (* An atom over an EMPTY sequence whose predicate's template has cells is
       true under every candidate the template can read back -- the universal
       over its positions has none -- so as a body assumption it says nothing
       and as a head it satisfies the clause outright.  Dropping it is exact
       for the family of candidates this expansion serves, and it is also what
       keeps an empty sequence from declining the exhaustive expansion, since
       it offers no cell to enumerate. *)
    let vacuous atom =
      match split_atom atom with
      | (ExAtom.PApp ((pvar, sorts), _) as core), _, params ->
          (match Map.Poly.find template_map (Ident.pvar_to_tvar pvar) with
          | Some t -> lambda_params_of t > List.length sorts
          | None -> false)
          && List.exists (own_arrays core params) ~f:(fun (_, arr) ->
                 vacuous_sequence arr)
      | _ -> false
    in
    if Set.exists clause.ExClause.positive ~f:vacuous then []
    else
    let clause =
      { clause with ExClause.negative = Set.filter clause.ExClause.negative ~f:(Fn.non vacuous) }
    in
    (* every head atom's arrays together, for the print below only *)
    let pos_arrays =
      List.concat_map (Set.to_list clause.ExClause.positive) ~f:(fun atom ->
          let core, _, params = split_atom atom in
          own_arrays core params)
    in
    (* What the abstraction is being given to learn from.  A cell abstraction
       reads the CONTENTS of the counterexample's array, so an array that is
       constant -- no stored index, one default everywhere -- is empty data: it
       cannot distinguish any index from any other, and an invariant whose
       content is a relation between indices is then unreachable from it however
       rich the qualifier space or however many index tuples are enumerated.
       Printed because nothing else in a run says it, and because it is the
       difference between an input the method can learn from and one it
       cannot. *)
    if not (List.is_empty pos_arrays) then
      Debug.print
      @@ lazy
           (sprintf "head example arrays: %s"
              (String.concat ~sep:" "
                 (List.map pos_arrays ~f:(fun (k, arr) ->
                      (* stores at EVERY level: a curried array written
                         [const (store ...)] stores nothing at the outermost
                         level and varies below it *)
                      let rec stores = function
                        | Leaf _ | Lam _ -> 0
                        | Node a ->
                            List.length a.stored
                            + stores a.defv
                            + List.sum (module Int) a.stored ~f:(fun (_, (_, n)) ->
                                  stores n)
                      in
                      sprintf "a%d(default=%s,stored=%d)" k
                        (match arr.defv with
                        | Leaf v -> Term.str_of (to_old_in arr v)
                        | Node _ -> "<array>"
                        | Lam _ -> "<lambda>")
                        (stores (Node arr))))));
    let expand_side atoms =
      List.map (Set.to_list atoms) ~f:(fun atom ->
          let core, wrap, params = split_atom atom in
          let updated, qpa, _idxs =
            extend_with_cells core (own_arrays core params) template_map
          in
          current_qpa := qpa;
          incr current_qpa_writes;
          wrap updated)
    in
    (* A goal example's body atoms at the cells their clause read, where a
       record exists ([celled_goal_at_reads]); the others, and every atom when
       the switch is off or the clause has a head, go through the ordinary
       expansion below exactly as before. *)
    let at_reads, rest_negative =
      if not (config.celled_goal_at_reads && Set.is_empty clause.ExClause.positive)
      then ([], clause.ExClause.negative)
      else
        Set.fold clause.ExClause.negative ~init:([], Set.Poly.empty)
          ~f:(fun (expanded, rest) atom ->
            match GoalReads.records_of_atom atom with
            | [] -> (expanded, Set.add rest atom)
            | records -> (
                let core, wrap, params = split_atom atom in
                match
                  expand_at_goal_reads core (own_arrays core params) template_map records
                with
                | Some atoms -> (expanded @ List.map atoms ~f:wrap, rest)
                | None -> (expanded, Set.add rest atom)))
    in
    let negative =
      let sampled () =
        List.concat
        @@ List.init num ~f:(fun _ ->
               expand_side rest_negative)
      in
      Set.Poly.of_list
      @@ (fun ordinary -> at_reads @ ordinary)
      @@
      if not config.celled_negative_exhaustive then sampled ()
      else if config.celled_over_bound_sweep then
        (* per atom: exhaustive where its product fits, the sweep where it is
           over the bound, and the sampler only for an atom that declines both
           -- one atom over the bound no longer samples the others *)
        List.concat_map (Set.to_list rest_negative) ~f:(fun atom ->
            let core, wrap, params = split_atom atom in
            let arrays = own_arrays core params in
            let sample_this () =
              List.concat
              @@ List.init num ~f:(fun _ -> expand_side (Set.Poly.singleton atom))
            in
            match expand_all_outcome ?qualifiers_map core arrays template_map with
            | Expanded atoms -> List.map atoms ~f:wrap
            | Declined -> sample_this ()
            | Over_bound { paths; per_array; related } -> (
                match sweep_atoms ~num core arrays ~paths ~per_array ~related with
                | Some atoms ->
                    current_qpa := 1;
                    incr current_qpa_writes;
                    List.map atoms ~f:wrap
                | None -> sample_this ()))
      else
        let enumerated =
          List.map (Set.to_list rest_negative) ~f:(fun atom ->
              let core, wrap, params = split_atom atom in
              Option.map ~f:(List.map ~f:wrap)
              @@ expand_all ?qualifiers_map core (own_arrays core params) template_map)
        in
        if List.exists enumerated ~f:Option.is_none then sampled ()
        else List.concat @@ List.filter_map enumerated ~f:Fn.id
    in
    (* [celled_goal_value_variants]: a goal example's celled body atoms (and,
       with [celled_step_body_value_variants], a step example's), each
       with its variants beside it.  An expanded atom is matched to the atom it
       was expanded from by predicate and by its leading arguments, which the
       expansion leaves as they were; one that matches none is kept alone. *)
    let negative =
      if
        not
          (offers_value_variants ~limit:config.celled_goal_value_variants
             ~step_bodies:config.celled_step_body_value_variants
             ~has_positive:(not (Set.is_empty clause.ExClause.positive)))
      then negative
      else
        let originals =
          List.filter_map (Set.to_list clause.ExClause.negative) ~f:(fun atom ->
              match split_atom atom with
              | (ExAtom.PApp ((pvar, sorts), args) as core), wrap, params ->
                  let paths = array_paths_of_sorts sorts in
                  if List.is_empty paths then None
                  else Some (pvar, args, paths, own_arrays core params, wrap)
              | _ -> None)
        in
        let extra_values args =
          List.filter_map args ~f:(fun t ->
              match LogicOld.T_int.let_int t with
              | v -> Some (Logic.IntTerm.mk_int v)
              | exception exn_ when not (Common.Timer.is_async exn_) -> None)
          @ List.init (max 1 config.cell_candidates_below_zero) ~f:(fun k ->
                Logic.IntTerm.mk_from_int (-(k + 1)))
        in
        let variants_of ((pvar, sorts), terms) =
          match
            List.find originals ~f:(fun (pvar', args, _, _, _) ->
                Stdlib.( = ) pvar pvar'
                && List.length terms > List.length args
                && Stdlib.( = ) (List.take terms (List.length args)) args)
          with
          | None -> []
          | Some (_, args, paths, arrays, wrap) ->
              let width = CellQual.total_cell_width paths in
              let extra = List.length terms - List.length args in
              if width = 0 || extra % width <> 0 then []
              else
                let qpa = extra / width in
                (* the cells in the order [expand] and [celled_atoms_of_tuples]
                   append them: per path, [qpa] columns of indices then value *)
                let segments =
                  List.concat_mapi paths ~f:(fun k path ->
                      List.init qpa ~f:(fun _ -> (k, CellQual.cell_width path)))
                in
                let _, slots =
                  List.fold_map segments ~init:(List.drop terms (List.length args))
                    ~f:(fun rest (k, w) ->
                      let seg, rest = List.split_n rest w in
                      let seg = List.map seg ~f:Logic.ExtTerm.of_old_term in
                      (rest, (k, (List.drop_last_exn seg, List.last_exn seg))))
                in
                List.map
                  (goal_cell_variants ~linked_first:config.celled_goal_linked_variants_first
                     ~paths ~arrays ~extra_values:(extra_values args)
                     ~level_terms:(fun si ->
                       List.map
                         (CellQual.terms_of_sort si (List.zip_exn args (List.take sorts (List.length args))))
                         ~f:(fun t -> Logic.ExtTerm.of_old_term @@ Evaluator.simplify_term t))
                     ~limit:config.celled_goal_value_variants slots)
                  ~f:(fun changes ->
                    let _, cells =
                      List.fold_map (List.zip_exn segments changes)
                        ~init:(List.drop terms (List.length args))
                        ~f:(fun rest ((k, w), change) ->
                          let seg, rest = List.split_n rest w in
                          ( rest,
                            match change with
                            | None -> seg
                            | Some (idxs, v) ->
                                let arr = Stdlib.List.assoc k arrays in
                                List.map (idxs @ [ v ]) ~f:(to_old_in arr) ))
                    in
                    wrap (ExAtom.PApp ((pvar, sorts), args @ List.concat cells)))
        in
        let added =
          List.concat_map (Set.to_list negative) ~f:(fun a ->
              match a with
              | ExAtom.PApp papp | ExAtom.PPApp (_, papp) -> variants_of papp
              | _ -> [])
        in
        Debug.print
        @@ lazy
             (sprintf "celled goal value variants: %d body atom(s), %d added"
                (Set.length negative) (List.length added));
        Set.union negative (Set.Poly.of_list added)
    in
    Debug.print
    @@ lazy
         (sprintf
            "celled expansion: %d body atom(s) from %d (%s), %d head atom(s),              %d variant(s)"
            (Set.length negative)
            (Set.length clause.ExClause.negative)
            (if config.celled_negative_exhaustive then "every candidate cell"
             else "sampled")
            (Set.length clause.ExClause.positive)
            num);
    (* What a celled atom's cell columns actually hold, printed so that the
       question "do the candidate cells of two arrays ever line up the way the
       intended invariant relates them" can be answered from a run instead of
       argued about.  With one array it is the index and value of each atom;
       with two it is the pair, and whether any pair satisfies a relation is
       what decides whether the examples admit an invariant that states one. *)
    Debug.print
    @@ lazy
         (String.concat ~sep:"\n"
         @@ List.map (Set.to_list negative) ~f:(fun a ->
                sprintf "celled body atom: %s" (ExAtom.str_of a)));
    let head_variants =
      let sampled () =
        List.init num ~f:(fun _ ->
            expand_side clause.ExClause.positive)
      in
      if config.celled_head_parametric then
        let parametric =
          List.map (Set.to_list clause.ExClause.positive) ~f:(fun atom ->
              let ground, wrap, params = split_atom atom in
              let arrays = own_arrays ground params in
              wrap
                (match
                   expand_parametric ~full:config.celled_head_parametric_full
                     ground arrays template_map
                 with
                | Some a -> a
                | None ->
                    let updated, _, _ =
                      extend_with_cells ground arrays template_map
                    in
                    updated))
        in
        if config.celled_head_parametric_full then
          (* the read is written out against the array, so this one clause is
             the whole of [forall j. phi] and nothing else is needed *)
          [ parametric ]
        else
          (* the quantified clause covers only the indices the array does not
             store; the stored ones are covered by the ground expansion, which
             is why both are emitted *)
          parametric
          :: (let enumerated =
                List.map (Set.to_list clause.ExClause.positive) ~f:(fun atom ->
                    let core, wrap, params = split_atom atom in
                    Option.map ~f:(List.map ~f:wrap)
                    @@ expand_all ?qualifiers_map ~wide:config.cell_candidates_from_args_in_head
                         core (own_arrays core params) template_map)
              in
              if List.exists enumerated ~f:Option.is_none then sampled ()
              else
                match List.filter_map enumerated ~f:Fn.id with
                | [] -> sampled ()
                | first :: _ as columns ->
                    List.init (List.length first) ~f:(fun k ->
                        List.filter_map columns ~f:(fun atoms -> List.nth atoms k)))
      else if not config.celled_positive_exhaustive then sampled ()
      else
        let enumerated =
          List.map (Set.to_list clause.ExClause.positive) ~f:(fun atom ->
              let core, wrap, params = split_atom atom in
              let arrays = own_arrays core params in
              Option.map ~f:(List.map ~f:wrap)
              @@
              if not config.celled_head_over_bound_sweep then
                expand_all ?qualifiers_map
                  ~wide:config.cell_candidates_from_args_in_head
                  ~extra_indices:head_witnesses core arrays template_map
              else
                (* [celled_head_over_bound_sweep]: over the bound, the
                   sweep's tuples are separate demands, each an instance of
                   the head's universal *)
                match
                  expand_all_outcome ?qualifiers_map
                    ~wide:config.cell_candidates_from_args_in_head
                    ~extra_indices:head_witnesses core arrays template_map
                with
                | Expanded atoms -> Some atoms
                | Declined -> None
                | Over_bound { paths; per_array; related } -> (
                    match
                      sweep_atoms ~num core arrays ~paths ~per_array ~related
                    with
                    | Some atoms ->
                        current_qpa := 1;
                        incr current_qpa_writes;
                        Some atoms
                    | None -> None))
        in
        if List.exists enumerated ~f:Option.is_none then sampled ()
        else
          match List.filter_map enumerated ~f:Fn.id with
          | [] -> sampled ()
          | first :: _ as columns ->
              List.init (List.length first) ~f:(fun k ->
                  List.filter_map columns ~f:(fun atoms -> List.nth atoms k))
    in
    List.map head_variants ~f:(fun positive ->
        ExClause.canon { positive = Set.Poly.of_list positive; negative }))

  (* The cache behind [celled_expansion_cache]: an example clause's celled
     expansion, reused across synthesis attempts.

     What the expansion reads, and therefore what the key must hold:
     - the example clause itself;
     - of the template map, only the number of binders of each template the
       clause's predicates have, which decides how many cells each atom takes
       -- so the key holds that count per predicate rather than the templates;
     - the indices earlier refutations named, when [cell_witness_indices]
       offers them, since they join every integer candidate set and they only
       grow during a run;
     - the recorded reads of the clause's body atoms, when
       [celled_goal_at_reads] expands a goal example at them, since they grow
       during a run too;
     - the indices recorded for the clause's head atoms, when
       [celled_head_at_witnesses] offers them, for the same reason;
     - the configuration, which is fixed for this module instance, and the
       process-global datatype and function environments, which the
       evaluation reads and which no synthesis attempt changes;
     - the cell sampler.  An expansion that drew from it is never stored:
       reusing it would hand every later attempt one draw where each would
       otherwise receive its own, and skipping the draw would shift every draw
       after it.  So only an expansion that consumed nothing from the sampler
       -- the exhaustive enumerations on both sides, or an atom with no cell --
       is reused, and with the flag on the constraints an attempt receives are
       those it would have built.
     Two things differ on a hit, neither of them the meaning: a parametric head
     expansion's index variables keep the names they were given when first
     built, which is a renaming of variables that the parametric example binds
     itself; and the diagnostics the expansion prints, the refuting-index
     report among them, are not printed again.  [current_qpa]'s last write is
     replayed, since the read-back falls back on it.

     Keyed by polymorphic comparison, which is structural here: an example
     clause is built in canonical shape, so equal clauses compare equal, and a
     clause that is not canonical can only miss, never hit the wrong entry.
     Per module instance, so per problem, and unguarded like the other state of
     this module ([cells_per_pred], [cell_random]): one instance is driven by
     one synthesis loop. *)
  let celled_expansion_cache :
      ( ExClause.t
        * (Ident.pvar * int option) list
        * Z.t list option
        * (GoalReads.record list list option * Z.t list),
        ExClause.t list * int option )
      Map.Poly.t
      ref =
    ref Map.Poly.empty

  let celled_clauses_of ?qualifiers_map ~num template_map (clause : ExClause.t) :
      ExClause.t list =
    (* The cache's key does not include the qualifiers, and either collapse of
       indices reads them, so the two are not combined: with the
       collapse on, every attempt expands afresh. *)
    if
      (not config.celled_expansion_cache)
      || config.celled_collapse_constant_indices
      || config.celled_collapse_default_indices
    then
      celled_clauses_of_uncached ?qualifiers_map ~num template_map clause
    else
      let key =
        ( clause,
          List.map (Set.to_list (ExClause.pvs_of clause)) ~f:(fun pvar ->
              ( pvar,
                Option.map ~f:Logic.Term.num_binds
                @@ Map.Poly.find template_map (Ident.pvar_to_tvar pvar) )),
          (if config.cell_witness_indices then Some (CellQual.witnesses ())
           else None),
          (* the recorded reads grow during a run (the resolver can add a
             record for an example already expanded), so they are part of what
             the expansion read *)
          ( (if config.celled_goal_at_reads then
               Some
                 (List.map (Set.to_list clause.ExClause.negative)
                    ~f:GoalReads.records_of_atom)
             else None),
            (* the head witnesses grow during a run too *)
            head_witnesses_of_clause clause ) )
      in
      match Map.Poly.find !celled_expansion_cache key with
      | Some (clauses, qpa_write) ->
          Option.iter qpa_write ~f:(fun q -> current_qpa := q);
          Debug.print
          @@ lazy
               (sprintf "celled expansion reused: %d clause(s)"
                  (List.length clauses));
          clauses
      | None ->
          let draws = !cell_random_draws and writes = !current_qpa_writes in
          let clauses = celled_clauses_of_uncached ?qualifiers_map ~num template_map clause in
          (if !cell_random_draws = draws then
             let qpa_write =
               if !current_qpa_writes = writes then None else Some !current_qpa
             in
             celled_expansion_cache :=
               Map.Poly.set !celled_expansion_cache ~key
                 ~data:(clauses, qpa_write));
          clauses

  (* Reconcile a predicate's recorded sort with the template generated for
     it: where the template took cell parameters, the sort has to admit them
     too, or every consumer that reads the arity off the sort disagrees with
     the term.  The count is read back from the term rather than from the
     template module's configuration, so the two halves cannot drift. *)
  let with_cells_in_sort ?pred sort term =
    let paths =
      array_paths_of_sorts
      @@ List.map ~f:Logic.ExtTerm.to_old_sort
      @@ Logic.Sort.args_of sort
    in
    let width = CellQual.total_cell_width paths in
    let arity = Logic.Sort.arity_of sort in
    let extras = lambda_params_of term - arity in
    if width = 0 || extras <= 0 then sort
    else begin
      assert (extras mod width = 0);
      current_qpa := extras / width;
      Option.iter pred ~f:(fun p ->
          Hashtbl.set cells_per_pred ~key:p ~data:(extras / width));
      (* the appended arguments take the sorts of the template's own cell
         binders, read off the term, which need not be integers *)
      let appended =
        List.map ~f:snd @@ List.drop (fst @@ Logic.Term.let_lam term) arity
      in
      let appended =
        if List.length appended = extras then appended
        else List.init extras ~f:(fun _ -> Logic.IntTerm.SInt)
      in
      extend_sort_with_sorts sort appended
    end

  (* Consecutive unsat cores whose labels blamed neither, for
     [force_bound_blame_after]. *)
  let unsats_without_updating_coefficients = ref 0
  let unsats_without_updating_consts = ref 0

  (* ------------------------------------------------------------------
     Reading back the quantifier prefix the solver chose.

     Where the template fixes [forall i_1..i_n], the QSAT route leaves the
     prefix open: the query declares one boolean [Q_i] per index and a [perm]
     asserted to be a bijection of [1..n], and the model says which quantifier
     each index got and in what order they are applied.  These rebuild the
     template's binders from that answer.

     Ported from an abandoned branch. *)

  (* [\ params. Q_1 x_1. … Q_n x_n. body] split into its three parts. *)
  let prefix_binds_of (t : Logic.term) =
    let params, quantified = Logic.Term.let_lam t in
    let binds, body = Logic.Term.let_quants quantified in
    (params, binds, body)

  let extract_permutation (model : Logic.model) : (int * int) list =
    List.filter_map model ~f:(fun ((tvar, _), term) ->
        match
          (Scanf.sscanf_opt (Ident.name_of_tvar tvar) "#perm-%d" Fun.id, term)
        with
        | Some pos, Some (Logic.Con (Logic.IntTerm.Int z, _)) ->
            (* [Z.to_int] is safe: the query asserts [perm] a bijection of
               [1..n], [n] the template's number of indices, so the model's
               value is a small position *)
            Some (pos, Z.to_int z)
        | _ -> None)

  (* [Q_i] true is universal.  A [Q_i] the model does not mention is a
     don't-care, and existential is the weaker reading of it. *)
  let extract_quantifiers (model : Logic.model) (t : Logic.term) =
    let _, binds, _ = prefix_binds_of t in
    List.init (List.length binds) ~f:(fun i ->
        match
          List.find model ~f:(fun ((tv, _), _) ->
              String.equal (Ident.name_of_tvar tv) (sprintf "Q%d" (i + 1)))
        with
        | Some ((_, sort), Some term) ->
            assert (Logic.BoolTerm.is_bool_sort sort);
            if Logic.BoolTerm.is_true term then Logic.Forall else Logic.Exists
        | _ -> Logic.Exists)

  (* UNREACHABLE BY DEFAULT (prefix synthesis). Replace the template's own
     prefix by the one the solver chose, binder for binder. *)
  let instantiate_quantifiers quantifiers (t : Logic.term) : Logic.term =
    let params, binds, body = prefix_binds_of t in
    assert (List.length binds = List.length quantifiers);
    Logic.Term.mk_lambda params @@ Logic.Term.mk_mixed_binds
      (List.map (List.zip_exn binds quantifiers) ~f:(fun ((_, tv, sort), q) ->
           (q, tv, sort)))
      body

  (* Apply the permutation by renaming the body's index variables, leaving the
     binders where they are -- which is the same predicate with its indices
     read in the chosen order. *)
  let reorder (perm : (int * int) list) (t : Logic.term) : Logic.term =
    let params, binds, body = prefix_binds_of t in
    let tvars = List.map binds ~f:(fun (_, v, _) -> v) in
    if List.length tvars <> List.length perm then t
    else
      let rename =
        Map.Poly.of_alist_exn
        @@ List.mapi tvars ~f:(fun i tv ->
               (tv, List.nth_exn tvars (Stdlib.List.assoc (i + 1) perm - 1)))
      in
      Logic.Term.mk_lambda params
      @@ Logic.Term.mk_mixed_binds binds (Logic.Term.rename rename body)

  (* The two together, for every template that has a prefix to choose.  The
     branch this comes from applied them to the one unknown its own benchmark
     named; every template that binds indices of its own is the general form
     of the same test. *)
  let with_chosen_prefix (model : Logic.model) (cand : Logic.cand_map) :
      Logic.cand_map =
    let perm = extract_permutation model in
    if List.is_empty perm then cand
    else
      Map.Poly.map cand ~f:(fun (sort, term) ->
          let _, binds, _ = prefix_binds_of term in
          if List.is_empty binds then (sort, term)
          else
            let term = reorder perm term in
            (sort, instantiate_quantifiers (extract_quantifiers model term) term))

  let get_key =
    let key_cnt = ref 0 in
    fun () ->
      incr key_cnt;
      sprintf "#S%d_%d" (match id with Some id -> id | None -> 0) !key_cnt

  type constr = parameter_update_type * Logic.term

  let threshold_ignore_bounds_constrs = 64 (*ToDo*)

  (* [oracle_example_probe]'s state: the verdict per example clause as the
     synthesis query stated it (a celled clause is its own key, so a clause
     expanded at other cells is checked afresh), the clauses of the current
     round, and what has been printed.  Written by [oracle_probe] and
     [oracle_probe_report] alone and read by nothing that decides. *)
  let oracle_probe_memo :
      (ExClause.t, OracleProbe.verdict * string list) Map.Poly.t ref =
    ref Map.Poly.empty

  let oracle_probe_round = ref (-1)

  (* the example clauses the constraints were generated from in the current
     round, each once however many synthesis attempts the round makes *)
  let oracle_probe_seen : (ExClause.t, OracleProbe.verdict) Map.Poly.t ref =
    ref Map.Poly.empty
  let oracle_probe_first_in_round : string option ref = ref None
  let oracle_probe_printed = ref None
  let oracle_probe_first_reported = ref false
  let oracle_probe_skips_reported : string Hash_set.t = Hash_set.create (module String)

  let oracle_probe (vs : VersionSpace.t) (clause : ExClause.t) =
    match vs.VersionSpace.oracle with
    | None ->
        if Hash_set.strict_add oracle_probe_skips_reported "none" |> Result.is_ok
        then
          Stdlib.prerr_endline
            "[oracle-probe] no oracle solution is loaded (set load_oracle_sol)"
    | Some (_, sol) ->
        if !oracle_probe_round <> !current_round then (
          oracle_probe_round := !current_round;
          oracle_probe_seen := Map.Poly.empty;
          oracle_probe_first_in_round := None);
        let oracle =
          Set.fold sol ~init:Map.Poly.empty ~f:(fun acc (pvar, pred) ->
              Map.Poly.set acc ~key:pvar ~data:pred)
        in
        let arity_of pvar =
          Option.map ~f:(Logic.Sort.args_of >> List.length)
          @@ Map.Poly.find (PCSP.Problem.senv_of APCSP.problem)
               (Ident.pvar_to_tvar pvar)
        in
        let paths_of = array_paths_of_sorts in
        let verdict, notes =
          match Map.Poly.find !oracle_probe_memo clause with
          | Some r -> r
          | None ->
              let eval phi =
                let phi = Evaluator.simplify phi in
                if Formula.is_true phi then Some true
                else if Formula.is_false phi then Some false
                  (* a quantifier left over a sequence, or a regular
                     expression, is a query Z3 may not return from within
                     any budget, and the alarm cannot interrupt it: a
                     diagnostic does not ask it *)
                else if Z3Smt.Z3interface.may_not_return phi then None
                else
                  try
                    match
                      Z3Smt.Z3interface.check_valid ~timeout:(Some 2000) ~id
                        vs.VersionSpace.fenv phi
                    with
                    | `Valid -> Some true
                    | `Invalid _ -> Some false
                    | _ -> None
                  with exn when not (Common.Timer.is_async exn) -> None
              in
              let r =
                OracleProbe.check ~eval ~oracle_of:(Map.Poly.find oracle)
                  ~arity_of ~paths_of clause
              in
              oracle_probe_memo := Map.Poly.set !oracle_probe_memo ~key:clause ~data:r;
              (match r with
              | OracleProbe.Violated, notes ->
                  Debug.print
                  @@ lazy
                       (sprintf
                          "[oracle probe] round %d: the oracle solution violates \
                           the example %s\n  offered cells: %s%s"
                          !current_round (ExClause.str_of clause)
                          (OracleProbe.str_of_offered ~arity_of ~paths_of clause)
                          (if List.is_empty notes then ""
                           else "\n  notes: " ^ String.concat ~sep:"; " notes))
              | OracleProbe.Undecided, _ ->
                  Debug.print
                  @@ lazy
                       (sprintf "[oracle probe] undecided on the example %s"
                          (ExClause.str_of clause))
              | OracleProbe.Skipped why, _ ->
                  if Hash_set.strict_add oracle_probe_skips_reported why |> Result.is_ok
                  then Stdlib.prerr_endline ("[oracle-probe] cannot check: " ^ why)
              | OracleProbe.Holds, _ -> ());
              r
        in
        oracle_probe_seen :=
          Map.Poly.set !oracle_probe_seen ~key:clause ~data:verdict;
        match verdict with
        | OracleProbe.Violated ->
            let preds =
              String.concat_map_set ~sep:"," (ExClause.pvs_of clause)
                ~f:Ident.name_of_pvar
            in
            if Option.is_none !oracle_probe_first_in_round then
              oracle_probe_first_in_round := Some preds;
            if not !oracle_probe_first_reported then (
              oracle_probe_first_reported := true;
              Stdlib.prerr_endline
              @@ sprintf
                   "[oracle-probe] first violated example (round %d, predicate(s) \
                    %s): %s\n[oracle-probe]   offered cells: %s%s"
                   !current_round preds (ExClause.str_of clause)
                   (OracleProbe.str_of_offered ~arity_of ~paths_of clause)
                   (if List.is_empty notes then ""
                    else "\n[oracle-probe]   notes: " ^ String.concat ~sep:"; " notes))
        | _ -> ()

  (* the round's tally, printed when it has changed since it was last printed *)
  let oracle_probe_report () =
    let line =
      let count f = Map.Poly.count !oracle_probe_seen ~f in
      let c, v, u, k =
        ( count (function OracleProbe.Skipped _ -> false | _ -> true),
          count (function OracleProbe.Violated -> true | _ -> false),
          count (function OracleProbe.Undecided -> true | _ -> false),
          count (function OracleProbe.Skipped _ -> true | _ -> false) )
      in
      sprintf
        "[oracle-probe] round %d: examples checked %d, violated %d, undecided \
         %d, skipped %d%s"
        !oracle_probe_round c v u k
        (match !oracle_probe_first_in_round with
        | None -> ""
        | Some p -> "; first violated on " ^ p)
    in
    if not (Option.equal String.equal (Some line) !oracle_probe_printed) then (
      oracle_probe_printed := Some line;
      Stdlib.prerr_endline line)

  let cgen_body ?(incremental = false) ?(temporary_sample = Set.Poly.empty)
      (* every caller now answers this from the instance its [csolve] will
         use ([take_param_cnstrs]); the default is [false] so that a caller
         which forgets adds nothing rather than adding bounds to a solver that
         already holds them *)
      ?(add_param_cnstrs = false) sample (vs : VersionSpace.t)
      ( (temp_param_senv : Logic.sort_env_map),
        (templates : (Ident.tvar, Logic.Sort.t * constr) Map.Poly.t),
        (temp_param_cnstrs :
          ( Ident.tvar,
            (bool * parameter_update_type * Logic.term) Set.Poly.t )
          Map.Poly.t),
        (qualifiers_map : qualifiers_map) ) =
    let templates =
      if true (*ToDo*) then templates
      else
        let pvs = ExClauseSet.pvs_of (Set.union sample temporary_sample) in
        Map.Poly.filter_keys templates ~f:(fun key ->
            Set.mem pvs (Ident.tvar_to_pvar key))
    in
    let tvar_update_map = Map.Poly.map templates ~f:(snd >> fst) in
    let templates =
      Map.Poly.map templates ~f:(fun (sort, (_, term)) -> (sort, term))
    in
    let template_map = Map.Poly.map templates ~f:snd in
    let temporary_constrs =
      Set.Poly.map temporary_sample ~f:(fun clause ->
          if print_log then
            Debug.print
            @@ lazy
                 (sprintf "gen temporary_constrs of temporary example: %s"
                 @@ ExClause.str_of clause);
          let constr =
            let unknowns =
              Set.filter (ExClause.tvs_of clause) ~f:(Map.Poly.mem templates)
            in
            if config.qsat_clause_constraints then
              Evaluator.simplify
              @@ replace_concrete_clause_with_QSAT vs template_map
                   qualifiers_map unknowns temp_param_senv clause
            else
              constr_of_pex vs template_map qualifiers_map unknowns
                temp_param_senv clause
          in
          if print_log then
            Debug.print
            @@ lazy (sprintf "temporary constr: %s" @@ Formula.str_of constr);
          constr)
    in
    let key_constr_map, key_tvar_update_list_map, key_clause_map =
      Set.fold
        ~init:
          (if incremental then
             (Map.Poly.empty, !ref_key_tvar_update_list_map, !ref_key_clause_map)
           else (Map.Poly.empty, Map.Poly.empty, Map.Poly.empty))
        sample
        ~f:(fun maps clause ->
          (* REACHABLE ON THE DEFAULT PATH, and unchanged there. The body below
             is the fold's former body verbatim; it is named so that the celled
             route can fold it over the several clauses one example becomes.
             With [celled_examples] at 0 it is applied exactly once per clause,
             as before. *)
          let update
              (key_constr_map, key_tvar_update_list_map, key_clause_map)
              (clause : ExClause.t) =
            let clause_started = Common.Clock.now_float () in
            if config.oracle_example_probe then oracle_probe vs clause;
            if print_log then
              Debug.print
              @@ lazy
                   (sprintf "gen constr of example: %s" @@ ExClause.str_of clause);
            (*let templates =
                  Map.Poly.mapi templates ~f:(fun ~key:tvar ~data:(sort, term) ->
                      let hole_qualifiers_map =
                        Map.Poly.find_exn qualifiers_map tvar
                      in
                      let hole_template_map =
                        hole_template_map_of hole_qualifiers_map
                          (Logic.Sort.args_of sort) ~f:(fun _senv -> Fn.id)
                      in
                      let sargs =
                        Logic.sort_env_list_of_sorts @@ Logic.Sort.args_of sort
                      in
                      ( sort,
                        Evaluator.simplify
                        @@ Logic.ExtTerm.to_old_formula Map.Poly.empty
                             (Map.force_merge temp_param_senv
                                (Map.Poly.of_alist_exn sargs))
                             (Logic.ExtTerm.subst hole_template_map term)
                             (List.map ~f:Logic.ExtTerm.of_old_term
                             @@ Term.of_sort_env
                             @@ List.map
                                  ~f:(fun (x, s) ->
                                    (x, Logic.ExtTerm.to_old_sort s))
                                  sargs) ))
                in
                Debug.print
                @@ lazy
                     (sprintf "templates: %s"
                     @@ String.concat_map_list ~sep:"\n" (Map.to_alist templates)
                          ~f:(fun (x, (_s, t)) ->
                            sprintf "%s: %s" (Ident.name_of_tvar x)
                              (Formula.str_of t)));*)
            let unknowns =
              Set.filter (ExClause.tvs_of clause) ~f:(Map.Poly.mem templates)
            in
            let update_map =
              Set.to_list
              @@ Set.Poly.map ~f:(fun tvar ->
                  (tvar, Map.Poly.find_exn tvar_update_map tvar))
              @@ Set.union unknowns
                   (Set.Poly.map (ExClause.pvs_of clause) ~f:Ident.pvar_to_tvar)
            in
            let key = get_key () in
            let constr =
              let constr, string_free =
                constr_of_pex_hinted vs template_map qualifiers_map unknowns
                  temp_param_senv clause
              in
              let constr =
                if config.seq_exist_instances <= 0 then constr
                else
                  CgenProfile.time 6 (fun () ->
                  Ast.SeqExistInst.rewrite
                    ~max_instances:config.seq_exist_instances constr)
              in
              incr CgenProfile.clauses;
              (*Z3Smt.Z3interface.simplify ~id (LogicOld.get_fenv ())
              @@*)
              (* [string_free] answers the question below without a traversal
                 where the constraint was assembled from shared pieces whose
                 own answers are known; it is never [true] where the question
                 would answer [true] *)
              if
                CgenProfile.time 7 (fun () -> (not string_free)
                && (Set.exists
                      (Formula.term_sort_env_of constr)
                      ~f:(snd >> Term.is_string_sort)
                   || Set.exists (Formula.funsyms_of constr) ~f:(function
                        | T_string.StrConst _ -> true
                        | _ -> false)))
              then
                (* ite expressions are eliminated if string theory is involved *)
                (* this causes a significant performance degradation when applied to other theories *)
                Evaluator.simplify @@ Formula.elim_ite constr
              else
                (* [constr] is already simplified; a second pass over it was
                   measured to change nothing on 49,405 constraints while costing
                   17% of constraint generation.  Only the [elim_ite] branch has
                   new structure to simplify.  Skipping the pass renames the
                   fresh variables allocated afterwards, which moves individual
                   CEGIS runs either way but not the aggregate (118 CHC files:
                   wall 0.91x, iterations 622 to 552, the same-binary control at
                   0.97x). *)
                constr
            in
            if RLCfg.config.enable && RLCfg.config.show_unsat_core then (
              RLConfig.lock ();
              Debug.print_stdout
              @@ lazy
                   (sprintf "labeled constraint: %s"
                   @@ Yojson.Safe.to_string
                   @@ lc_to_yojson { label = key; constr = Formula.str_of constr }
                   );
              RLConfig.unlock ());
            if print_log then
              Debug.print
              @@ lazy (sprintf "** constr: [%s] %s" key (Formula.str_of constr));
            (if
               Lazy.force SharingCensus.on
               && Set.exists
                    (Set.union clause.ExClause.positive clause.ExClause.negative)
                    ~f:holds_exact_step_index
             then
               SharingCensus.run
                 ~label:
                   (sprintf "constraint, %d positive, %d negative"
                      (Set.length clause.ExClause.positive)
                      (Set.length clause.ExClause.negative))
                 constr);
            (if Lazy.force CgenProfile.on then
               let d =
                 Time_float.Span.to_sec
                   (Time_float.diff (Common.Clock.now_float ()) clause_started)
               in
               if Float.(d >= 2.) then
                 Stdlib.prerr_endline
                 @@ sprintf
                      "[cgen-profile] slow clause %.3f s: %d positive, %d negative atoms, constraint size %d"
                      d
                      (Set.length clause.ExClause.positive)
                      (Set.length clause.ExClause.negative)
                      (Formula.ast_size constr));
            ( Map.Poly.add_exn key_constr_map ~key ~data:constr,
              Map.Poly.add_exn key_tvar_update_list_map ~key ~data:update_map,
              Map.Poly.add_exn key_clause_map ~key ~data:clause )
          in
          if config.celled_examples <= 0 then update maps clause
          else
            (* one clause becomes several, each with its own concrete cells *)
            List.fold ~init:maps ~f:update
            @@ (fun l -> CgenProfile.celled := !CgenProfile.celled + List.length l; l)
            @@ CgenProfile.time 0 @@ fun () -> CellArray.expand_if_celled
                 ~celled:(template_has_cells template_map)
                 ~expand:
                   (celled_clauses_of ~qualifiers_map
                      ~num:config.celled_examples template_map)
                 clause)
    in
    if config.oracle_example_probe && Option.is_some vs.VersionSpace.oracle then
      oracle_probe_report ();
    let key_constr_map, key_tvar_update_list_map =
      (* the fn-predicate and template-parameter bounds constraints are
         asserted once per (incremental) SMT instance: by default on the first
         call after the templates were (re)initialized, which serves the default
         instance; a caller using another instance must ask for them itself *)
      if add_param_cnstrs then
        let key_constr_map, key_tvar_update_list_map =
          let constr, tvs =
            if Stdlib.(config.fn_goal_constraint = Config.Omit) then
              (Formula.mk_true (), Set.Poly.empty)
            else if
              Map.Poly.existsi templates ~f:(fun ~key ~data:_ ->
                  match
                    Map.Poly.find (PCSP.Problem.kind_map_of APCSP.problem) key
                  with
                  | Some k -> Kind.(is_int_fun k || is_real_fun k || is_regex k)
                  | _ -> false)
            then (Formula.mk_true (), Set.Poly.empty)
            else
              let fn_templates =
                Map.Poly.filter_mapi templates
                  ~f:(fun ~key:tvar ~data:(sort, term) ->
                    match
                      Map.Poly.find
                        (PCSP.Problem.kind_map_of APCSP.problem)
                        tvar
                    with
                    | Some k when Kind.is_fn k ->
                        let hole_qualifiers_map =
                          Map.Poly.find_exn qualifiers_map tvar
                        in
                        let hole_template_map =
                          hole_template_map_of hole_qualifiers_map
                            (Logic.Sort.args_of sort) ~f:(fun _senv -> Fn.id)
                        in
                        Some (sort, Logic.ExtTerm.subst hole_template_map term)
                    | _ -> None)
              in
              let fmls, tvss =
                List.unzip @@ Set.to_list
                @@ Set.Poly.filter_map (PCSP.Problem.clauses_of APCSP.problem)
                     ~f:(fun (uni_senv, pos, neg, phi) ->
                       if
                         Set.is_empty pos
                         && Set.for_all neg
                              ~f:
                                ( Logic.Term.let_apps >> function
                                  | Var (tvar, _), [ Var _ ] -> (
                                      match
                                        Map.Poly.find
                                          (PCSP.Problem.kind_map_of
                                             APCSP.problem)
                                          tvar
                                      with
                                      | Some k -> Kind.is_fn k
                                      | _ -> false)
                                  | _ -> false )
                       then (
                         if false then
                           Debug.print
                           @@ lazy
                                (sprintf "fn clause: %s"
                                   (Clause.str_of
                                      (PCSP.Problem.senv_of APCSP.problem)
                                      (uni_senv, pos, neg, phi)));
                         let eqs, sub =
                           let map =
                             Set.to_list
                             @@ Set.Poly.map neg
                                  ~f:
                                    ( Logic.ExtTerm.subst
                                        (Map.Poly.map fn_templates ~f:snd)
                                    >> Logic.ExtTerm.to_old_fml Map.Poly.empty
                                         (Map.force_merge uni_senv
                                            temp_param_senv)
                                    >> Formula.let_atom >> fst
                                    >> Atom.let_psym_app
                                    >> function
                                      | T_bool.Eq, [ Term.Var (x, _s, _); t ], _
                                        ->
                                          if false then
                                            Debug.print
                                            @@ lazy
                                                 (sprintf "fn pred sub: %s = %s"
                                                    (Ident.name_of_tvar x)
                                                    (Term.str_of t));
                                          (x, t)
                                      | _ -> assert false )
                           in
                           List.fold ~init:([], Map.Poly.empty)
                             ~f:(fun (eqs, map) -> function
                             | [] -> assert false
                             | (x, t) :: xtss ->
                                 let ys =
                                   List.map xtss ~f:(fun _ ->
                                       Ident.mk_fresh_tvar ())
                                 in
                                 let s = Term.sort_of t in
                                 let ytss =
                                   (x, t)
                                   :: List.map2_exn ys xtss ~f:(fun y (_, s) ->
                                       (y, s))
                                 in
                                 ( eqs
                                   @ List.map ys ~f:(fun y ->
                                       Formula.eq (Term.mk_var x s)
                                         (Term.mk_var y s)),
                                   Map.force_merge map
                                     (Map.Poly.of_alist_exn ytss) ))
                           @@ List.classify
                                (fun (x1, _) (x2, _) -> Ident.tvar_equal x1 x2)
                                map
                         in
                         let fml =
                           Evaluator.simplify (*@@ Formula.elim_ite*)
                           @@ Formula.subst sub
                           @@ Formula.mk_imply (Formula.and_of eqs)
                           @@ Logic.ExtTerm.to_old_fml
                                (PCSP.Problem.senv_of APCSP.problem)
                                uni_senv phi
                         in
                         (* the clause's variables the substitution left are
                            universal in the clause; free here they would be
                            existential to the solver *)
                         let fml =
                           match config.fn_goal_constraint with
                           | Config.Universal ->
                               FnGoalClosure.close ~uni_senv fml
                           | Config.Existential | Config.Omit -> fml
                         in
                         if false then
                           Debug.print
                           @@ lazy
                                (sprintf "fn pred constr: %s"
                                   (Formula.str_of fml));
                         let tvs =
                           Set.Poly.filter_map neg
                             ~f:
                               ( Logic.Term.let_apps >> function
                                 | Var (tvar, _), [ Var _ ] -> (
                                     match
                                       Map.Poly.find
                                         (PCSP.Problem.kind_map_of APCSP.problem)
                                         tvar
                                     with
                                     | Some k ->
                                         if Kind.is_fn k then Some tvar
                                         else None
                                     | _ -> None)
                                 | _ -> None )
                         in
                         Some (fml, tvs))
                       else None)
              in
              (Formula.and_of fmls, Set.Poly.union_list tvss)
          in
          if Formula.is_true constr then
            (key_constr_map, key_tvar_update_list_map)
          else
            let key = get_key () in
            if print_log then
              Debug.print
              @@ lazy
                   (sprintf "** fn pred constr: [%s] %s" key
                      (Formula.str_of constr));
            ( Map.Poly.add_exn key_constr_map ~key ~data:constr,
              Map.Poly.add_exn key_tvar_update_list_map ~key
                ~data:
                  (Set.to_list
                  @@ Set.Poly.map tvs ~f:(fun tvar -> (tvar, Shape))) )
        in
        Map.Poly.fold temp_param_cnstrs
          ~init:(key_constr_map, key_tvar_update_list_map)
          ~f:(fun ~key:tvar ~data (key_constr_map, key_tvar_update_list_map) ->
            Set.fold ~init:(key_constr_map, key_tvar_update_list_map) data
              ~f:(fun
                  (key_constr_map, key_tvar_update_list_map)
                  (is_hard, update_label, cnstr)
                ->
                let param_constr =
                  Evaluator.simplify
                  @@ Logic.ExtTerm.to_old_fml Map.Poly.empty temp_param_senv
                       cnstr
                in
                if
                  Formula.is_true param_constr
                  || (not is_hard)
                     &&
                     match Map.Poly.find templates tvar with
                     | None -> false (*ToDo*)
                     | Some (s, _) ->
                         List.length (Logic.Sort.args_of s)
                         >= threshold_ignore_bounds_constrs
                then (key_constr_map, key_tvar_update_list_map)
                else
                  let key = get_key () in
                  if RLCfg.config.enable && RLCfg.config.show_unsat_core then (
                    RLConfig.lock ();
                    Debug.print_stdout
                    @@ lazy
                         (sprintf "labeled bounds constraint: %s"
                         @@ Yojson.Safe.to_string
                         @@ lc_to_yojson
                              {
                                label = key;
                                constr = Formula.str_of param_constr;
                              });
                    RLConfig.unlock ());
                  if print_log then
                    Debug.print
                    @@ lazy
                         (sprintf "** bounds constr: [%s] %s" key
                            (Formula.str_of param_constr));
                  ( Map.Poly.add_exn key_constr_map ~key ~data:param_constr,
                    Map.Poly.add_exn key_tvar_update_list_map ~key
                      ~data:[ (tvar, update_label) ] )))
      else (key_constr_map, key_tvar_update_list_map)
    in
    let key_constr_map =
      if true then key_constr_map
      else
        let phi = UTermEnv.to_formula vs.uenv in
        if Formula.is_true phi then key_constr_map
        else if
          Map.Poly.exists key_constr_map ~f:(fun phi1 ->
              Stdlib.(Formula.str_of phi1 = Formula.str_of phi))
        then key_constr_map
        else
          let key = get_key () in
          if print_log then
            Debug.print
            @@ lazy (sprintf "uterm_constr %s: %s" key (Formula.str_of phi));
          Map.Poly.add_exn key_constr_map ~key ~data:phi
    in
    if incremental then (
      ref_key_tvar_update_list_map := key_tvar_update_list_map;
      ref_key_clause_map := key_clause_map);
    Debug.print @@ lazy "constraints generated";
    ( temporary_constrs,
      key_constr_map,
      key_tvar_update_list_map,
      key_clause_map,
      templates,
      tvar_update_map,
      temp_param_senv,
      qualifiers_map )

  (* [cgen_body] with the per-atom memo active for exactly its duration, and
     inside one datatype-conversion scope ([Logic.ExtTerm.with_shared_datatype_conversion]):
     every term and formula conversion between the two representations the
     call makes -- one per literal of a shared-parameter reading, one per
     clause constraint, one per qualifier share -- reuses the datatype values
     already converted instead of converting each datatype graph again.  The
     scope's contract is that sharing changes no result (a conversion is a
     function of its argument and datatype values are immutable), so the
     constraints are the same values; only the time differs.  Measured on a
     Thrust input whose clauses carry nested tuple, reference and option
     datatypes, the datatype conversion was about a sixth of constraint
     generation. *)
  let cgen ?incremental ?temporary_sample ?add_param_cnstrs sample vs arg =
    Logic.ExtTerm.with_shared_datatype_conversion @@ fun () ->
    atom_constr_memo := Some (ref Map.Poly.empty);
    hole_naming :=
      if config.celled_step_exact_name_groups then Some (HoleNaming.create ())
      else None;
    Hashtbl.clear template_shape_ok;
    Hashtbl.clear guard_entries;
    CgenProfile.reset ();
    let t0 = Common.Clock.now_float () in
    let draws0 = !cell_random_draws in
    Exn.protect
      ~finally:(fun () -> atom_constr_memo := None; hole_naming := None;
        if Lazy.force CgenProfile.on then
          Stdlib.prerr_endline
          @@ sprintf "[cgen-profile] cell sampler draws %d"
               (!cell_random_draws - draws0);
        CgenProfile.report ~incremental:(Option.value incremental ~default:false)
          (Time_float.Span.to_sec (Time_float.diff (Common.Clock.now_float ()) t0)))
      ~f:(fun () ->
        Common.PhaseTime.with_phase "cgen" (fun () ->
            cgen_body ?incremental ?temporary_sample ?add_param_cnstrs sample vs
              arg))

  (* Contract: [model] is a model of the query [inst]'s solver holds
     together with [temporary_constrs]; the result is a model of the same
     constraints (the first one if no bounded call succeeds) whose count of
     nonzero qualifier keys is no larger.  Every bounded call is pushed and
     popped around its bound, so the solver is left as it was found.  At most
     [config.shrink_candidate_literals] calls are made. *)
  let shrink_qualifier_literals (inst : smt_solver_instance) ~temporary_constrs
      (qualifiers_map : qualifiers_map) model =
    let keys =
      List.dedup_and_sort ~compare:Ident.tvar_compare
      @@ List.concat_map (Map.Poly.data qualifiers_map)
           ~f:(List.concat_map ~f:(snd >> List.map ~f:fst))
    in
    let key_value model k =
      List.find_map model ~f:(fun ((x, _), t_opt) ->
          if Stdlib.(x = k) then t_opt else None)
    in
    (* an absent key is one the solver did not care about, which the
       candidate reads as zero *)
    let nonzero model =
      List.count keys ~f:(fun k ->
          match key_value model k with
          | None -> false
          | Some t when T_int.is_int t -> not (Z.equal (T_int.let_int t) Z.zero)
          | Some _ -> true)
    in
    let count =
      T_int.mk_sum (T_int.zero ())
      @@ List.map keys ~f:(fun k ->
          T_bool.ifte
            (Formula.neq (Term.mk_var k T_int.SInt) (T_int.zero ()))
            (T_int.one ()) (T_int.zero ()))
    in
    let ask mid =
      if List.is_empty keys then None
      else
        match
          Z3Smt.Z3interface.incr_check_sat_unsat_core ~id ~enable:false
            ~timeout:(Some config.shrink_candidate_timeout)
            ~non_tracked:
              (Set.add temporary_constrs
                 (Formula.leq count (T_int.mk_int (Z.of_int mid))))
            inst.solver inst.ctx inst.z3fenv inst.z3dtenv Map.Poly.empty
        with
        | `Sat model' -> Some model'
        | _ -> None
    in
    let n0 = nonzero model in
    let model, n =
      ShrinkSearch.run ~max_calls:config.shrink_candidate_literals
        ~count:nonzero ~ask model
    in
    Debug.print
    @@ lazy (sprintf "shrink_candidate_literals: %d -> %d nonzero keys" n0 n);
    model

  (* The reading of the synthesis solver's assertions that
     [drop_qualifier_literals] reuses across rounds: an assertion is the same
     Z3 term from one round to the next, so its tree over interned constants
     is built once per solver.  Reset when the instance's solver is renewed. *)
  let drop_reading :
      (Z3.Solver.solver
      * (int, (KeyEval.t option * int list)) Hashtbl.t
      * (string, int) Hashtbl.t)
      option
      ref =
    ref None

  (* Contract: [model] is a model of the query [inst]'s solver holds together
     with [temporary_constrs]; the result is [model] with some nonzero
     integer qualifier keys set to zero, such that every one of those
     constraints that evaluated to [true] under [model] still does.  A
     constraint an earlier round tracked comes back from the solver as
     [label => e] with [label] free, and the check enforces it, so it is read
     as [e].  No solver is asked and the solver is left as it was found: each
     constraint is read once into an OCaml tree over its constants and
     evaluated under the model's values; one that cannot be read or does not
     evaluate to [true] -- a constant the model does not assign, a
     quantifier, an array, an uninterpreted function -- blocks every key it
     mentions.  A key the model does not assign is read as zero, as the
     candidate reads it.  Every candidate kept is a model of the same
     constraints, so soundness is unaffected: validation checks every
     candidate. *)
  let drop_qualifier_literals (inst : smt_solver_instance) ~temporary_constrs
      (qualifiers_map : qualifiers_map) model =
    let started = Common.Clock.now_float () in
    let ctx = inst.ctx in
    let reading, names =
      match !drop_reading with
      | Some (solver, reading, names) when phys_equal solver inst.solver ->
          (reading, names)
      | _ ->
          let r = Hashtbl.create (module Int) and n = Hashtbl.create (module String) in
          drop_reading := Some (inst.solver, r, n);
          (r, n)
    in
    let intern name =
      match Hashtbl.find names name with
      | Some i -> i
      | None ->
          let i = Hashtbl.length names in
          Hashtbl.set names ~key:name ~data:i;
          i
    in
    let is_uninterp_const e =
      Z3.Expr.is_const e
      && Stdlib.(
           Z3.FuncDecl.get_decl_kind (Z3.Expr.get_func_decl e)
           = Z3enums.OP_UNINTERPRETED)
    in
    let name_of e =
      Z3.Symbol.to_string (Z3.FuncDecl.get_name (Z3.Expr.get_func_decl e))
    in
    (* a variable's Z3 name, as the converter spells it *)
    let z3_name x s =
      try
        let e =
          Z3Smt.Z3interface.of_term ~id ctx [] [] inst.z3fenv inst.z3dtenv
            (Term.mk_var x s)
        in
        if is_uninterp_const e then Some (name_of e) else None
      with exn_ when not (Common.Timer.is_async exn_) -> None
    in
    let quals =
      List.dedup_and_sort
        ~compare:(fun (k1, _) (k2, _) -> Ident.tvar_compare k1 k2)
      @@ List.concat_map (Map.Poly.data qualifiers_map)
           ~f:
             (List.concat_map
                ~f:(snd >> List.map ~f:(fun (k, (_, _, phi)) -> (k, phi))))
    in
    let key_value k =
      List.find_map model ~f:(fun ((x, _), t_opt) ->
          if Stdlib.(x = k) then t_opt else None)
    in
    let nonzero =
      List.filter quals ~f:(fun (k, _) ->
          match key_value k with
          | Some t when T_int.is_int t -> not (Z.equal (T_int.let_int t) Z.zero)
          | _ -> false)
    in
    (* each key's interned index *)
    let key_of_index = Hashtbl.create (module Int) in
    let index_of_key = Hashtbl.Poly.create () in
    List.iter quals ~f:(fun (k, _) ->
        Option.iter (z3_name k T_int.SInt) ~f:(fun n ->
            let i = intern n in
            Hashtbl.set key_of_index ~key:i ~data:k;
            Hashtbl.set index_of_key ~key:k ~data:i));
    let strip e =
      if Z3.Boolean.is_implies e then
        match Z3.Expr.get_args e with
        | [ label; body ] when is_uninterp_const label && Z3.Boolean.is_bool label
          ->
            body
        | _ -> e
      else e
    in
    let conv =
      Z3Smt.Z3interface.of_formula_with_z3fenv ~id ctx [] [] inst.z3fenv
        inst.z3dtenv
    in
    let read e =
      let i = Z3.AST.get_id (Z3.Expr.ast_of_expr e) in
      match Hashtbl.find reading i with
      | Some r -> r
      | None ->
          let consts = ref Int.Set.empty in
          let tree =
            KeyEval.of_expr (strip e) ~key:(fun c ->
                let j = intern (name_of c) in
                consts := Set.add !consts j;
                Some j)
          in
          let r = (tree, Set.to_list !consts) in
          Hashtbl.set reading ~key:i ~data:r;
          r
    in
    let assertions =
      Array.of_list
      @@ List.map ~f:read (Z3.Solver.get_assertions inst.solver)
      @ List.map (Set.to_list temporary_constrs) ~f:(fun phi ->
          try
            let e = conv phi in
            (* this round's own: not worth keeping *)
            let consts = ref Int.Set.empty in
            let tree =
              KeyEval.of_expr e ~key:(fun c ->
                  let j = intern (name_of c) in
                  consts := Set.add !consts j;
                  Some j)
            in
            (tree, Set.to_list !consts)
          with exn_ when not (Common.Timer.is_async exn_) -> (None, []))
    in
    (* the model's values by interned index; a key it does not assign is
       zero, any other constant it does not assign has no value *)
    let base_values = Array.create ~len:(Hashtbl.length names) None in
    List.iter model ~f:(fun ((x, s), t_opt) ->
        Option.iter t_opt ~f:(fun t ->
            let v =
              if T_int.is_int t then Some (KeyEval.VN (Q.of_bigint (T_int.let_int t)))
              else if T_real.is_real t then Some (KeyEval.VN (T_real.let_real t))
              else if T_bool.is_true t then Some (KeyEval.VB true)
              else if T_bool.is_false t then Some (KeyEval.VB false)
              else None
            in
            Option.iter v ~f:(fun v ->
                Option.iter (z3_name x s) ~f:(fun n ->
                    match Hashtbl.find names n with
                    | Some i when i < Array.length base_values ->
                        base_values.(i) <- Some v
                    | _ -> ()))));
    Hashtbl.iteri key_of_index ~f:(fun ~key:i ~data:_ ->
        if i < Array.length base_values && Option.is_none base_values.(i) then
          base_values.(i) <- Some (KeyEval.VN Q.zero));
    let nonzero_set = Set.Poly.of_list (List.map nonzero ~f:fst) in
    let index = Hashtbl.Poly.create () in
    let mentioning = ref 0 and native = ref 0 in
    Array.iteri assertions ~f:(fun i (tree, consts) ->
        let ks =
          List.filter_map consts ~f:(fun j ->
              Option.bind (Hashtbl.find key_of_index j) ~f:(fun k ->
                  if Set.mem nonzero_set k then Some k else None))
        in
        if not (List.is_empty ks) then (
          incr mentioning;
          if Option.is_some tree then incr native;
          List.iter ks ~f:(fun k -> Hashtbl.add_multi index ~key:k ~data:i)));
    let prepared = Common.Clock.now_float () in
    (* each assertion that mentions a nonzero key, compiled under the model;
       one with no tree or not true under the model is blocked *)
    let compiled = Hashtbl.create (module Int) in
    let forest = KeyEval.forest () in
    let blocked = ref Int.Set.empty in
    let live =
      let nonzero_indices =
        Int.Set.of_list
        @@ List.filter_map nonzero ~f:(fun (k, _) -> Hashtbl.find index_of_key k)
      in
      Set.mem nonzero_indices
    in
    Hashtbl.iter index ~f:(fun is ->
        List.iter is ~f:(fun i ->
            if not (Hashtbl.mem compiled i || Set.mem !blocked i) then
              match fst assertions.(i) with
              | Some tree ->
                  let c = KeyEval.compile ~forest ~live base_values tree in
                  if Stdlib.(c.cur = Some (KeyEval.VB true)) then
                    Hashtbl.set compiled ~key:i ~data:c
                  else blocked := Set.add !blocked i
              | None -> blocked := Set.add !blocked i));
    let blocked = !blocked in
    let compiled_at = Common.Clock.now_float () in
    let tree_nodes =
      let rec size (c : KeyEval.inc) =
        Array.fold c.args ~init:1 ~f:(fun n a -> n + size a)
      in
      Hashtbl.fold compiled ~init:0 ~f:(fun ~key:_ ~data:c n -> n + size c)
    in
    (* the values of the zeros accepted so far; [holds] is asked about the
       accepted set plus the keys it is given, so only those keys change *)
    let cur_values = Array.copy base_values in
    let foreign =
      let consts =
        lazy
          (Set.Poly.of_list
          @@ List.filter_map (Lazy.force problem_int_consts) ~f:(fun t ->
                 if T_int.is_int t then Some (T_int.let_int t) else None))
      in
      fun phi ->
        Set.exists (Formula.funsyms_of phi) ~f:(function
          | T_int.Int n ->
              let a = Z.abs n in
              Z.gt a Z.one && not (Set.mem (Lazy.force consts) a)
          | _ -> false)
    in
    (* foreign constants first, then the higher ranks, then by name *)
    let order =
      List.map ~f:fst
      @@ List.stable_sort
           ~compare:(fun (k1, phi1) (k2, phi2) ->
             let f1 = foreign phi1 and f2 = foreign phi2 in
             if Bool.(f1 <> f2) then if f1 then -1 else 1
             else
               let c = Rank.compare (Rank.rank_of phi2) (Rank.rank_of phi1) in
               if c <> 0 then c else Ident.tvar_compare k1 k2)
           nonzero
    in
    (* a key no readable assertion true under the model can be checked on,
       or that some blocked assertion mentions, is kept without a question;
       an assertion that is not compiled into [forest] is one of those, so
       every root [update] reaches is a compiled assertion, true before the
       change *)
    let certainly_kept k =
      match Hashtbl.find index_of_key k with
      | None -> true
      | Some _ ->
          List.exists (Hashtbl.find_multi index k) ~f:(fun i ->
              Set.mem blocked i || not (Hashtbl.mem compiled i))
    in
    let asked, stuck = List.partition_tf order ~f:(Fn.non certainly_kept) in
    let holds _zeroed ks =
      let roots =
        KeyEval.update forest cur_values
          (List.map ks ~f:(fun k ->
               (Core.Hashtbl.find_exn index_of_key k, Some (KeyEval.VN Q.zero))))
      in
      let ok =
        List.for_all roots ~f:(fun r ->
            Option.equal Bool.equal (KeyEval.holds_root r) (Some true))
      in
      if ok then KeyEval.commit forest else KeyEval.rollback forest cur_values;
      ok
    in
    (* blocks pay when most keys go: a rejected block costs the union of its
       keys' paths and is asked again as halves.  Measured on two inputs: at
       about 500 keys with about 8 kept, blocks took a round's drop from about
       3 s to 0.8 s; at about 33 keys with about 8 kept over a 468,000-node
       query, blocks cost about 72,000 node updates a question and 4.6 s a
       round *)
    let blocks = List.length asked >= 64 in
    let zeroed, kept, irredundant, calls, passes =
      DropSearch.run ~blocks ~holds asked
    in
    let kept =
      let k = Set.Poly.of_list (kept @ stuck) in
      List.filter order ~f:(Set.mem k)
    in
    Debug.print
    @@ lazy
         (sprintf
            "drop_candidate_literals: %d -> %d nonzero keys (%d oracle calls, \
             %d passes, blocks %b, irredundant %b, %d kept unasked, %d node updates; \
             %d of %d assertions mention a nonzero \
             key, %d of them readable, %d not true under the model; %.3f s, \
             %.3f s of it reading the query, %.3f s compiling to %d nodes)\n\
             kept: %s"
            (List.length nonzero) (List.length kept) calls passes blocks irredundant
            (List.length stuck) forest.updated
            !mentioning (Array.length assertions) !native (Set.length blocked)
            (Time_float.Span.to_sec (Time_float.diff (Common.Clock.now_float ()) started))
            (Time_float.Span.to_sec (Time_float.diff prepared started))
            (Time_float.Span.to_sec (Time_float.diff compiled_at prepared))
            tree_nodes
            (String.concat_map_list ~sep:"; " kept ~f:(fun k ->
                 let phi = List.Assoc.find_exn quals ~equal:Stdlib.( = ) k in
                 let sign =
                   match key_value k with
                   | Some t when T_int.is_int t && Z.lt (T_int.let_int t) Z.zero
                     ->
                       "not "
                   | _ -> ""
                 in
                 sprintf "%s: %s%s" (Ident.name_of_tvar k) sign
                   (Formula.str_of phi))));
    if Set.is_empty zeroed then model
    else
      List.map model ~f:(fun (((x, _) as b), t_opt) ->
          if Set.mem zeroed x then (b, Some (T_int.zero ())) else (b, t_opt))

  let synth_query_dump_count = ref 0

  (* With COAR_DUMP_SYNTH_CHECK=<dir> set, every Z3 check a synthesis query
     makes is written as <dir>/check_<pid>_<n>_<k>.smt2 just before it is
     asked -- the solver's own assertions, tracked ones as the implications Z3
     keeps -- and its answer and the check's own wall time are appended, so the
     time excludes building and converting the constraints.  Nothing is written
     without the variable. *)
  let synth_check_dump_count = ref 0

  let with_synth_check_dump f =
    match Sys.getenv "COAR_DUMP_SYNTH_CHECK" with
    | None | Some "" -> f ()
    | Some dir ->
        let n = Stdlib.( ! ) synth_check_dump_count + 1 in
        Stdlib.( := ) synth_check_dump_count n;
        Z3Smt.Z3interface.with_query_dump
          (sprintf "%s/check_%d_%d" dir (Pid.to_int (Core_unix.getpid ())) n)
          f

  let rec csolve ?(ucore = true) ?(again = false)
      (smt_solver_instance : smt_solver_instance) arg =
    if not (Lazy.force CgenProfile.on) then
      csolve_body ~ucore ~again smt_solver_instance arg
    else
      let t0 = Common.Clock.now_float () in
      let (_, kcm, _, _, _, _, _, _) = arg in
      let res = csolve_body ~ucore ~again smt_solver_instance arg in
      Stdlib.prerr_endline @@ sprintf "[csolve-profile] constraints %d size %d %s %.3f"
        (Map.Poly.length kcm)
        (Map.Poly.fold kcm ~init:0 ~f:(fun ~key:_ ~data acc ->
             acc + Formula.ast_size data))
        ((match res with Candidate _ -> "candidate" | UnsatCore _ -> "unsatcore")
        ^ if again then " (re-ask)" else "")
        (Time_float.Span.to_sec (Time_float.diff (Common.Clock.now_float ()) t0));
      res

  (* [again]: [arg] was handed to this instance by the previous call, which
     asserted its tracked constraints and left them there; nothing is
     asserted again, so the question asked is that call's question.  Only
     meaningful right after that call, with nothing asked in between. *)
  and csolve_body ?(ucore = true) ?(again = false)
      (smt_solver_instance : smt_solver_instance)
      ( temporary_constrs,
        key_constr_map,
        key_tvar_update_list_map,
        key_clause_map,
        templates,
        tvar_update_map,
        temp_param_senv,
        qualifiers_map ) =
    (* With COAR_DUMP_SYNTH_QUERY=<dir> set, each synthesis query is written to
       <dir>/synth_<pid>_<n>.smt2 before it is asked (the process id keeps a
     forked copy's queries apart from its parent's) -- the solver's accumulated
       assertions with their tracking labels asserted, the tracked constraints
       and the temporary ones, all as plain assertions -- and its answer and wall time are appended after it.  The
       check itself tracks and pushes inside the Z3 interface, so this is the
       one place that holds every part of the query as it is asked; without the
       variable nothing is built. *)
    last_query_timed_out := false;
    declare_reached_in smt_solver_instance
      (Map.Poly.data key_constr_map @ Set.to_list temporary_constrs);
    let dump_started = Common.Clock.now_float () in
    let dump_file =
      match Sys.getenv "COAR_DUMP_SYNTH_QUERY" with
      | None | Some "" -> None
      | Some dir ->
          let n = Stdlib.( ! ) synth_query_dump_count + 1 in
          Stdlib.( := ) synth_query_dump_count n;
          let file =
            sprintf "%s/synth_%d_%d.smt2" dir
              (Pid.to_int (Core_unix.getpid ()))
              n
          in
          let ctx = smt_solver_instance.ctx in
          let s = Z3.Solver.mk_solver ctx None in
          let earlier = Z3.Solver.get_assertions smt_solver_instance.solver in
          Z3.Solver.add s earlier;
          (* a constraint an earlier round tracked comes back as [label => e]
             with [label] free, and the check enforces it; so do the dump *)
          List.iter earlier ~f:(fun e ->
              if Z3.Boolean.is_implies e then
                match Z3.Expr.get_args e with
                | label :: _
                  when Z3.Expr.is_const label && Z3.Boolean.is_bool label ->
                    Z3.Solver.add s [ label ]
                | _ -> ());
          let conv =
            Z3Smt.Z3interface.of_formula_with_z3fenv ~id ctx [] []
              smt_solver_instance.z3fenv smt_solver_instance.z3dtenv
          in
          Map.Poly.iter key_constr_map ~f:(fun phi ->
              if not (Formula.is_true phi) then Z3.Solver.add s [ conv phi ]);
          Set.iter temporary_constrs ~f:(fun phi ->
              Z3.Solver.add s [ conv phi ]);
          (* the example clause behind each tracked constraint, one comment
             line each, so that a free constant of the query can be traced to
             the example it came from *)
          let examples =
            Map.Poly.to_alist key_clause_map
            |> List.map ~f:(fun (key, cl) ->
                sprintf "; example %s: %s\n" key
                  (String.substr_replace_all ~pattern:"\n" ~with_:" "
                     (ExClause.str_of cl)))
            |> String.concat
          in
          (* and, per tracked constraint, whether it comes from an example
             clause or is one the round adds itself (bounds, the functional
             goal constraint), with its size and its free variables *)
          let examples =
            examples
            ^ String.concat
                (List.map (Map.Poly.to_alist key_constr_map)
                   ~f:(fun (key, phi) ->
                     sprintf "; tracked %s: %s, size %d, %d free variables\n"
                       key
                       (if Map.Poly.mem key_clause_map key then "example"
                        else "other")
                       (Formula.ast_size phi)
                       (Set.length (Formula.term_sort_env_of phi))))
          in
          Out_channel.write_all file
            ~data:
              (sprintf "; synthesis query %d: %d tracked, %d temporary, timeout %s\n%s%s\n(check-sat)\n"
                 n (Map.Poly.length key_constr_map)
                 (Set.length temporary_constrs)
                 (Option.value_map smt_solver_instance.smt_timeout ~default:"none"
                    ~f:string_of_int)
                 examples
                 (Z3.Solver.to_string s));
          Some file
    in
    let dump_result r =
      Option.iter dump_file ~f:(fun file ->
          Out_channel.with_file file ~append:true ~f:(fun oc ->
              Out_channel.output_string oc
                (sprintf "; answer: %s in %.3f s\n" r
                   (Time_float.Span.to_sec
                      (Time_float.diff (Common.Clock.now_float ()) dump_started)))))
    in
    match
      (fun r ->
        dump_result
          (match r with
          | `Sat _ -> "sat"
          | `Unsat _ -> "unsat"
          | `Timeout -> "timeout"
          | `Unknown reason -> "unknown (" ^ reason ^ ")");
        r)
      @@ with_synth_check_dump
      @@ fun () ->
      Common.PhaseTime.with_phase "check" @@ fun () ->
      Z3Smt.Z3interface.incr_check_sat_unsat_core ~id
        ~enable:(ucore && config.compute_ucores)
        ~timeout:
          (match PCSatCommon.SolveDeadline.remaining_ms_strict () with
          | None -> smt_solver_instance.smt_timeout
          | Some left ->
              (* capped, not stored: the doubling on a timeout builds on the
                 instance's own value *)
              Some
                (Option.value_map smt_solver_instance.smt_timeout ~default:left
                   ~f:(Int.min left)))
        ~non_tracked:temporary_constrs ~asserted:again
        ?fresh_labels:
          (if
             config.synthesis_fresh_solver_per_check
             || config.synthesis_fresh_solver_after_undecided
           then Some smt_solver_instance.tracked_labels
           else None)
        ~fresh_after_undecided:
          (config.synthesis_fresh_solver_after_undecided
          && not config.synthesis_fresh_solver_per_check)
        ~oneshot_first_ms:config.synthesis_oneshot_first_ms
        ~arith_solver:config.synthesis_arith_solver
        ~qvars:
          (if not config.synthesize_quantifier_prefix then Map.Poly.empty
           else
             (* how many indices each template binds; the query defines the
                prefix over that many *)
             Map.Poly.filter ~f:(fun n -> n > 0)
             @@ Map.Poly.map templates ~f:(fun (_, term) ->
                    let _, binds, _ = prefix_binds_of term in
                    List.length binds))
        smt_solver_instance.solver smt_solver_instance.ctx
        smt_solver_instance.z3fenv smt_solver_instance.z3dtenv key_constr_map
    with
    | `Sat model ->
        Debug.print @@ lazy "sat";
        let model =
          if config.shrink_candidate_literals <= 0 then model
          else
            shrink_qualifier_literals smt_solver_instance ~temporary_constrs
              qualifiers_map model
        in
        let model =
          if not config.drop_candidate_literals then model
          else
            drop_qualifier_literals smt_solver_instance ~temporary_constrs
              qualifiers_map model
        in
        (* with COAR_DUMP_SYNTH_QUERY, the model the candidate is read from
           is appended to the query's dump: every assigned template parameter,
           and for each qualifier key its hole and qualifier, so a nonzero
           key can be traced to the literal it puts in the candidate *)
        Option.iter dump_file ~f:(fun file ->
            let key_qual = Hashtbl.Poly.create () in
            Map.Poly.iter qualifiers_map ~f:(fun holes ->
                List.iter holes ~f:(fun (hole, kqs) ->
                    List.iter kqs ~f:(fun (k, (_, _, phi)) ->
                        Hashtbl.Poly.set key_qual ~key:k ~data:(hole, phi))));
            Out_channel.with_file file ~append:true ~f:(fun oc ->
                List.iter model ~f:(fun ((x, _), t_opt) ->
                    match t_opt with
                    | None -> ()
                    | Some t ->
                        let q =
                          match Hashtbl.Poly.find key_qual x with
                          | Some (hole, phi) ->
                              sprintf " hole %s qual %s" (Ident.name_of_tvar hole)
                                (Formula.str_of phi)
                          | None -> ""
                        in
                        Out_channel.output_string oc
                          (sprintf "; model %s = %s%s\n" (Ident.name_of_tvar x)
                             (Term.str_of t) q))));
        let model =
          List.map model ~f:(fun ((x, s), t_opt) ->
              ( (x, Logic.ExtTerm.of_old_sort s),
                Option.(t_opt >>= (Logic.ExtTerm.of_old_term >> return)) ))
        in
        let cand, certs =
          Common.PhaseTime.with_phase "candidate" (fun () ->
              candidate_of_model temp_param_senv templates qualifiers_map model)
        in
        (* the cells were columns of the hypothesis space, not arguments of
           the predicate: the candidate says what the array holds at an index,
           so it is read back as a read of that array *)
        (* REACHABLE ON THE DEFAULT PATH, identity there: both rewrites below
           are the ported mechanisms' last step and are skipped when their
           field is off, leaving the candidate exactly as [candidate_of_model]
           produced it. *)
        let cand =
          if config.celled_examples <= 0 then cand else cell_to_array cand
        in
        (* the prefix was the solver's to choose, so the candidate is not the
           template's prefix but the one the model names *)
        let cand =
          if config.synthesize_quantifier_prefix then
            with_chosen_prefix model cand
          else cand
        in
        Candidate (cand, certs)
    | `Unsat unsat_keys ->
        Debug.print
        @@ lazy ("unsat, reason:" ^ String.concat ~sep:"," unsat_keys);
        let unsat_keys =
          if ucore && config.compute_ucores then
            List.map unsat_keys ~f:(fun s ->
                String.sub s ~pos:1 ~len:(String.length s - 2))
          else Map.Poly.keys key_clause_map (* ToDo *)
        in
        let ucores =
          Set.Poly.of_list
          @@ List.filter_map unsat_keys ~f:(fun key ->
              Map.Poly.find key_clause_map key)
        in
        if ucore && config.compute_ucores then
          Debug.print
          @@ lazy (sprintf "*** unsat cores:\n%s" (ExClauseSet.str_of ucores));
        if RLCfg.config.enable && RLCfg.config.show_unsat_core then (
          RLConfig.lock ();
          Debug.print_stdout
          @@ lazy
               (sprintf "unsat cores: %s" @@ Yojson.Safe.to_string
               @@ ucores_to_yojson unsat_keys);
          RLConfig.unlock ());
        (* [relaxing] is [false] in every shipped configuration, and then the
           fold below is exactly the one that was here before: the bookkeeping
           the starvation relaxation needs -- which of the coefficient and
           constant bounds this core blamed -- is skipped entirely rather than
           computed and discarded. *)
        let relaxing = config.force_bound_blame_after > 0 in
        let update_coefficients = ref false in
        let update_consts = ref false in
        let pvar_labels_map =
          List.fold unsat_keys ~init:Map.Poly.empty ~f:(fun map key ->
              match Map.Poly.find key_tvar_update_list_map key with
              | Some pvar_update_list ->
                  List.fold pvar_update_list ~init:map
                    ~f:(fun map (pvar, label) ->
                      if relaxing then
                        (* by name, because the label's type is extensible and
                           each template module adds its own constructors, so a
                           consumer cannot match another module's [Coeff] *)
                        (match
                           Template.PredicateArrays.str_of_param_update_type
                             label
                         with
                        | "Coeff" ->
                            unsats_without_updating_coefficients := 0;
                            update_coefficients := true
                        | "Const" ->
                            unsats_without_updating_consts := 0;
                            update_consts := true
                        | _ -> ());
                      Map.Poly.update map pvar ~f:(function
                        | Some labels -> Set.add labels label
                        | None -> Set.Poly.singleton label))
              | None -> map)
        in
        let pvar_labels_map =
          if not relaxing then pvar_labels_map
          else begin
            if not !update_coefficients then incr unsats_without_updating_coefficients;
            if not !update_consts then incr unsats_without_updating_consts;
            let relax counter every label map =
              if !counter < every then map
              else begin
                counter := 0;
                Map.Poly.map map ~f:(Fn.flip Set.add label)
              end
            in
            relax unsats_without_updating_consts
              (500 * config.force_bound_blame_after)
              Template.PredicateArrays.Const
            @@ relax unsats_without_updating_coefficients
                 config.force_bound_blame_after Template.PredicateArrays.Coeff
                 pvar_labels_map
          end
        in
        let pvar_labels_map =
          pvar_labels_map |> Map.Poly.to_alist
          |> List.classify (fun (pvar1, _) (pvar2, _) ->
              if
                PCSP.Problem.is_parity_pred APCSP.problem pvar1
                && PCSP.Problem.is_parity_pred APCSP.problem pvar2
              then
                match
                  ( PCSP.Problem.kind_of APCSP.problem pvar1,
                    PCSP.Problem.kind_of APCSP.problem pvar2 )
                with
                | Kind.Parity (nwf1, _), Kind.Parity (nwf2, _) ->
                    Ident.tvar_equal nwf1.Kind.name nwf2.Kind.name
                | _, _ -> assert false
              else if
                PCSP.Problem.is_nwf_pred APCSP.problem pvar1
                && PCSP.Problem.is_nwf_pred APCSP.problem pvar2
              then
                match
                  ( PCSP.Problem.kind_of APCSP.problem pvar1,
                    PCSP.Problem.kind_of APCSP.problem pvar2 )
                with
                | Kind.NWF (nwf1, _), Kind.NWF (nwf2, _) ->
                    Ident.tvar_equal nwf1.Kind.name nwf2.Kind.name
                | _, _ -> assert false
              else Ident.tvar_equal pvar1 pvar2)
          |> List.fold ~init:Map.Poly.empty ~f:(fun map pvar_labels_list ->
              let pvar, _ = List.hd_exn pvar_labels_list in
              let labels =
                Set.Poly.union_list @@ List.map pvar_labels_list ~f:snd
              in
              Map.Poly.update map pvar ~f:(function
                | Some labels' -> Set.union labels' labels
                | None -> labels))
        in
        UnsatCore (ucores, pvar_labels_map)
    (*| `Unknown _reason -> (*failwith reason*)(*UnsatCore Map.Poly.empty*) (*ToDo*)*)
    | `Unknown reason ->
        Debug.print @@ lazy ("unknown:" ^ reason);
        UnsatCore
          ( Set.Poly.empty,
            Map.Poly.map tvar_update_map ~f:(fun _ ->
                Set.Poly.singleton TimeOut) )
    | (exception Timer.Timeout (*ToDo: not properly handled*)) | `Timeout ->
        Debug.print
        @@ lazy
             ("timeout: "
             ^ Option.value_map ~default:"none" ~f:string_of_int
                 smt_solver_instance.smt_timeout);
        (* give this solver instance twice the budget next time, and only this
           one: the call sites hand [csolve] different instances -- the default
           one, one per partial-solution target, and throwaways -- and a budget
           shared between them means a hard query against one target relaxes
           the deadline for every other.

           What happens next: this answer labels every predicate [TimeOut],
           which every template module ignores, so the shape is unchanged; the
           caller then regenerates the templates and renews every instance.
           With [keep_timeout_budget_across_rebuild] off, the renewal puts the
           configured budget back, so the doubled value set here is never read
           and the same query (fresh parameter names, same shape, same
           examples) is asked again at the configured budget.  With it on, that
           timeout-only rebuild keeps the doubled budget, and the doubling is
           capped by [max_synthesis_timeout] (default four times the configured
           budget). *)
        smt_solver_instance.smt_timeout <-
          SynthesisBudget.after_timeout
            ~keep:
              (config.keep_timeout_budget_across_rebuild
              || config.reask_on_timeout_without_rebuild)
            ~cap:synthesis_timeout_cap smt_solver_instance.smt_timeout;
        last_query_timed_out := true;
        UnsatCore
          ( Set.Poly.empty,
            Map.Poly.map tvar_update_map ~f:(fun _ ->
                Set.Poly.singleton TimeOut) )

  let initialize_templates ~ucore vs =
    let init =
      (Map.Poly.empty, Map.Poly.empty, Map.Poly.empty, Map.Poly.empty)
    in
    Map.Poly.fold (PCSP.Problem.senv_of APCSP.problem) ~init
      ~f:(fun
          ~key:tvar
          ~data:sort
          (temp_param_senv, template_map, temp_param_cnstrs, quals_map)
        ->
        let (module FT) = Map.Poly.find_exn template_modules tvar in
        let pvar = Ident.tvar_to_pvar tvar in
        let template, temp_param_cnstrs', temp_param_senv', hole_qualifiers_map
            =
          FT.gen_template ~ucore @@ VersionSpace.hspace_of_pvar pvar vs
        in
        let celled =
          CellArray.has_cell_columns ~arity:(Logic.Sort.arity_of sort) (snd template)
        in
        let tt = table_of ~celled vs pvar in
        (* The rows of the extended table carry the template's cell columns, so
           the parameters its qualifiers are read against are the template's
           own -- the predicate's parameters followed by the cells -- and not
           the predicate's alone.  Taken from a hole's qualifier rather than
           rebuilt, so that the two cannot disagree.

           Restricted to the template's LEADING lambda binders, because those
           are what a celled atom's arguments are substituted for.  A template
           that quantifies inside its body (quantifiers per array) builds its
           holes over the index variables as well, placed between the
           predicate's parameters and the cells; kept in the list they made it
           one longer than every celled atom, and the substitution refused.
           Left out, a qualifier reading an index variable has that variable
           free at every row and is recorded undecided -- which is what the
           uncelled table does with the same qualifiers, its list being the
           predicate's parameters alone.  Where the template binds nothing
           under its lambdas the filter is the identity. *)
        (if config.celled_examples > 0 && celled then
           match hole_qualifiers_map with
           | (_, (_, (env, _)) :: _) :: _ ->
               let lambda_params =
                 List.map ~f:fst @@ fst @@ Logic.Term.let_lam (snd template)
               in
               TruthTable.set_params tt
                 (List.filter env ~f:(fun (x, _) ->
                      List.mem lambda_params x ~equal:Ident.tvar_equal))
           | _ -> ());
        (match FT.kind_cert_template () with
        | Some c ->
            ref_cert_templates :=
              Map.Poly.update !ref_cert_templates tvar ~f:(function
                | None -> [ c ]
                | Some l -> c :: l)
        | None -> ());
        let hole_qualifiers_map =
          List.map hole_qualifiers_map ~f:(fun (tvar, quals) ->
              ( tvar,
                List.map quals ~f:(fun (tvar, (env, phi)) ->
                    ( tvar,
                      ( TruthTable.index_of_qual
                          ~print:
                            (if print_log then Debug.print ~id else fun _ -> ())
                          ~id tt vs.fenv
                          (VersionSpace.qdeps_of pvar vs)
                          phi,
                        env,
                        phi ) )) ))
        in
        ( Map.force_merge temp_param_senv temp_param_senv',
          Map.Poly.add_exn template_map ~key:tvar
            (* REACHABLE ON THE DEFAULT PATH: the guard's [else] is the sort
               the predicate was declared with, which is what was recorded
               here before. *)
            ~data:
              ( (if config.celled_examples <= 0 then sort
                 else with_cells_in_sort ~pred:tvar sort (snd template)),
                template ),
          List.fold temp_param_cnstrs' ~init:temp_param_cnstrs
            ~f:(fun acc elem ->
              match Map.Poly.find acc tvar with
              | None ->
                  Map.Poly.add_exn acc ~key:tvar ~data:(Set.Poly.singleton elem)
              | Some data ->
                  Map.Poly.set acc ~key:tvar ~data:(Set.add data elem)),
          Map.Poly.add_exn quals_map ~key:tvar ~data:hole_qualifiers_map ))

  let reduce_quals_terms vs =
    if config.reduce_quals_terms then (
      let reduced_quals_map =
        Hashtbl.Poly.map vs.VersionSpace.truth_table ~f:(fun tt ->
            let qlist = List.init (TruthTable.length_of_quals tt) ~f:Fn.id in
            let alist =
              Map.Poly.of_alist_exn
              @@ List.init (TruthTable.length_of_atoms tt) ~f:(fun i ->
                  (i, 0 (* dummy *)))
            in
            Set.Poly.of_list
            @@ List.map ~f:(IncrArray.get tt.qarr)
            @@ TruthTable.reduced_qlist_of ~require_evidence:true tt (qlist, alist))
      in
      let reduced_terms_map = VersionSpace.terms_map_of (*ToDo*) vs in
      let changed = ref false in
      Map.Poly.iteri template_modules ~f:(fun ~key ~data:(module FT) ->
          let pvar = Ident.tvar_to_pvar key in
          let reduced_quals = Hashtbl.Poly.find_exn reduced_quals_map pvar in
          let reduced_terms = Hashtbl.Poly.find_exn reduced_terms_map pvar in
          let hspace = VersionSpace.hspace_of_pvar pvar vs in
          changed :=
            !changed
            || (not (Set.eqlen reduced_quals hspace.quals))
            || not (Set.eqlen reduced_terms hspace.terms);
          let hspace =
            { hspace with quals = reduced_quals; terms = reduced_terms }
          in
          VersionSpace.set_hspace key hspace vs);
      !changed)
    else false

  let quals_terms_map =
    Map.Poly.mapi template_modules ~f:(fun ~key ~data:(module FT) ->
        let pvar = Ident.tvar_to_pvar key in
        let quals =
          match Map.Poly.find extracted_qualifiers pvar with
          | Some (_, quals) -> quals
          | None -> Set.Poly.empty
        in
        let terms =
          match Map.Poly.find extracted_terms pvar with
          | Some (_, terms) -> terms
          | None -> Set.Poly.empty
        in
        let consts =
          match Map.Poly.find extracted_consts pvar with
          | Some consts -> consts
          | None -> Set.Poly.empty
        in
        let quals, terms =
          if true then (
            Debug.print
            @@ lazy
                 (sprintf "adjusting qualifiers for %s:\n%s\n"
                    (Ident.name_of_tvar key)
                    (String.concat_map_set ~sep:"\n" ~f:Formula.str_of quals));
            Debug.print
            @@ lazy
                 (sprintf "adjusting terms for %s:\n%s\n"
                    (Ident.name_of_tvar key)
                    (String.concat_map_set ~sep:"\n" ~f:Term.str_of terms)));
          (* adjust the extracted qualifiers and terms to establish the initial qualifiers and terms *)
          Common.PhaseTime.with_phase "adjust-quals-terms" (fun () ->
              FT.adjust_quals_terms (quals, terms))
        in
        if true then (
          Debug.print
          @@ lazy
               (sprintf "adding qualifiers for %s @ init:\n%s\n"
                  (Ident.name_of_tvar key)
                  (String.concat_map_set ~sep:"\n" ~f:Formula.str_of quals));
          Debug.print
          @@ lazy
               (sprintf "adding terms for %s @ init:\n%s\n"
                  (Ident.name_of_tvar key)
                  (String.concat_map_set ~sep:"\n" ~f:Term.str_of terms));
          Debug.print
          @@ lazy
               (sprintf "adding constants for %s @ init:\n%s\n"
                  (Ident.name_of_tvar key)
                  (String.concat_map_set ~sep:"\n" ~f:Term.str_of consts)));
        (ref quals, ref terms, ref consts))

  let update_hspaces vs =
    Map.Poly.iteri template_modules ~f:(fun ~key ~data:(module FT) ->
        let name = Ident.name_of_tvar key in
        Debug.print @@ lazy ("** updating the hypothesis space of " ^ name);
        let ref_quals, ref_terms, ref_consts =
          Map.Poly.find_exn quals_terms_map key
        in
        let hspace =
          Common.PhaseTime.with_phase "update-hspace" @@ fun () ->
          FT.update_hspace
            {
              (VersionSpace.hspace_of_pvar (Ident.Pvar name) vs) with
              params = FT.params_of ();
              quals = !ref_quals;
              terms = !ref_terms;
              consts = !ref_consts;
            }
        in
        Debug.print
        @@ lazy
             (sprintf "[%s](%s):\n#quals: %d\n#terms: %d\n#consts: %d\n%s" name
                (str_of_sort_env_list Term.str_of_sort hspace.params)
                (Set.length hspace.quals) (Set.length hspace.terms)
                (Set.length hspace.consts) (FT.str_of ()));
        if false then
          Debug.print @@ lazy (VersionSpace.str_of_hspace name hspace);
        VersionSpace.set_hspace key hspace vs);
    (* a census line, read by nothing *)
    if Option.is_some (Sys.getenv "COAR_EXTRACT_CENSUS") then
      eprintf "[hspace-census] normal forms reused=%d computed=%d quals=%d\n%!"
        (Atomic.get HypSpace.normalize_memo_hits)
        (Atomic.get HypSpace.normalize_memo_misses)
        (Map.Poly.fold template_modules ~init:0 ~f:(fun ~key ~data:_ n ->
             n
             + Set.length
                 (VersionSpace.hspace_of_pvar
                    (Ident.Pvar (Ident.name_of_tvar key))
                    vs)
                   .quals));
    Common.PhaseTime.with_phase "truth-table" @@ fun () ->
    VersionSpace.update_truth_table
      ~print:(if print_log then Debug.print ~id else fun _ -> ())
      ~id vs

  let out_space_of () =
    Map.Poly.keys
    @@ Map.Poly.filter template_modules ~f:(fun (module FT) ->
        Fn.non FT.in_space ())

  let is_non_redundant_partial_sol vs key cand =
    Debug.print
    @@ lazy
         (sprintf "*** check if the cand partial sol of [%s] is non-redundant"
         @@ Ident.name_of_tvar key);
    let z3_expr_of smt_instance =
      Z3Smt.Z3interface.of_formula_with_z3fenv smt_instance.ctx [] []
        smt_instance.z3fenv smt_instance.z3dtenv
    in
    let sol =
      PCSP.Problem.sol_of_candidate APCSP.problem @@ CandSol.make cand
    in
    let smt_instance =
      Map.Poly.find_exn partial_sol_checking_smt_instance key
    in
    Set.exists
      (Map.Poly.find_exn
         (PCSP.Problem.partial_sol_targets_of APCSP.problem)
         key)
      ~f:(fun rand_info ->
        let term = Map.Poly.find_exn sol rand_info.PCSP.Params.name in
        let params =
          List.mapi ~f:(fun i (_, s) -> (Ident.Tvar (sprintf "x%d" i), s))
          @@ fst @@ Logic.ExtTerm.let_lam term
        in
        let uni_senv = Map.Poly.of_alist_exn params in
        let args = List.map params ~f:(fst >> Logic.ExtTerm.mk_var) in
        declare_reached_in smt_instance
          (Logic.ExtTerm.to_old_formula Map.Poly.empty uni_senv term args
          :: Option.value_map (VersionSpace.lower_bound_of vs key) ~default:[]
               ~f:(fun old_term ->
                 [
                   Logic.ExtTerm.to_old_formula Map.Poly.empty uni_senv
                     old_term args;
                 ]));
        (match VersionSpace.lower_bound_of vs key with
        | None -> ()
        | Some old_term ->
            Z3Smt.Z3interface.z3_solver_add smt_instance.solver
            @@ List.return
            @@ z3_expr_of ~id smt_instance
            @@ Formula.mk_neg
            @@ Logic.ExtTerm.to_old_formula Map.Poly.empty uni_senv old_term
                 args);
        Z3.Solver.push smt_instance.solver;
        Z3Smt.Z3interface.z3_solver_add smt_instance.solver
        @@ List.return
        @@ z3_expr_of ~id smt_instance
        @@ Logic.ExtTerm.to_old_formula Map.Poly.empty uni_senv term args;
        let ret =
          (* check whether [term] is subsumed by [old_term] *)
          match Z3Smt.Z3interface.z3_check smt_instance.solver [] with
          | Z3.Solver.SATISFIABLE -> true
          | _ -> false
        in
        Z3.Solver.pop smt_instance.solver 1;
        ret)

  let partial_candidates_of diff_sample vs =
    let open PCSP.Params in
    let target_pvars =
      Map.key_set @@ PCSP.Problem.partial_sol_targets_of APCSP.problem
    in
    if Set.is_empty target_pvars then []
    else (
      Debug.print @@ lazy "generating partial candidates";
      let diff_sample =
        (* filter out query clauses *)
        Set.Poly.map diff_sample ~f:(fun ex ->
            ( ex,
              Set.Poly.filter_map ~f:(function
                | ClauseGraph.Clause c -> Some c
                | _ -> None)
              @@ ClauseGraph.pred_clause_vertexs_of
                   vs.VersionSpace.examples.graph
              @@ ClauseGraph.Example ex ))
      in
      let rand_examples (* positive examples used instead of query claues *) =
        let get_random_parameter bound pvar sargs vs =
          let table = Hashtbl.Poly.find_exn vs.VersionSpace.truth_table pvar in
          List.mapi sargs ~f:(fun i s ->
              if Array.length table.aarr <= 0 then
                Logic.ExtTerm.random_term_of bound s
              else
                let ri = Random.int @@ Array.length table.aarr in
                match ExAtom.to_old_atom table.aarr.(ri) with
                | Some (_, Atom.App (_, ts, _))
                  when Set.is_empty @@ Term.tvs_of @@ List.nth_exn ts i ->
                    Logic.ExtTerm.of_old_term @@ List.nth_exn ts i
                | _ -> Logic.ExtTerm.random_term_of bound s)
        in
        Map.Poly.map
          (PCSP.Problem.partial_sol_targets_of APCSP.problem)
          ~f:
            (Set.concat_map ~f:(fun rand_info ->
                 let exi_senv = PCSP.Problem.senv_of APCSP.problem in
                 match Map.Poly.find exi_senv rand_info.name with
                 | None -> Set.Poly.empty
                 | Some sort ->
                     let sargs = Logic.Sort.args_of sort in
                     Set.Poly.of_list
                     @@ List.init rand_info.random_ex_size ~f:(fun _ ->
                         ExClause.mk_unit_pos
                         @@ ExAtom.of_old_atom exi_senv (Formula.mk_true ())
                         @@ Logic.ExtTerm.to_old_atm exi_senv Map.Poly.empty
                         @@ Logic.ExtTerm.mk_var_app rand_info.name
                         @@ get_random_parameter rand_info.random_ex_bound
                              (Ident.tvar_to_pvar rand_info.name)
                              sargs vs)))
      in
      let res =
        Map.Poly.data
        @@ Map.Poly.filter_mapi rand_examples ~f:(fun ~key ~data ->
            Debug.print
            @@ lazy
                 (sprintf "*** rand examples of [%s]\n%s"
                    (Ident.name_of_tvar key) (ExClauseSet.str_of data));
            let diff_ex =
              let f =
                Clause.must_be_satisfied ~print:Debug.print target_pvars
                @@ Map.Poly.find_exn
                     (PCSP.Problem.dep_graph_of APCSP.problem)
                     key
              in
              Set.Poly.filter_map diff_sample ~f:(fun (ex, cl) ->
                  if Set.for_all cl ~f then Some ex else None)
            in
            Debug.print
            @@ lazy (sprintf "used examples of [%s]" @@ Ident.name_of_tvar key);
            Debug.print @@ lazy (ExClauseSet.str_of diff_ex);
            let instance = Map.Poly.find_exn partial_sol_smt_instance key in
            let add_param_cnstrs = take_param_cnstrs instance in
            match
              csolve ~ucore:false instance
              @@ cgen ~incremental:true ~add_param_cnstrs ~temporary_sample:data
                   diff_ex vs !ref_templates
            with
            | Candidate (cand, certs) ->
                VersionSpace.set_kind_certs vs certs;
                if is_non_redundant_partial_sol vs key cand then (
                  Debug.print
                  @@ lazy
                       (sprintf
                          "*** generated a new candidate partial solution for \
                           [%s]"
                       @@ Ident.name_of_tvar key);
                  Some (cand, key))
                else None
            | UnsatCore _ -> None)
      in
      Debug.print @@ lazy "*** all candidate partial solutions generated";
      res)

  let print_truth_table = false

  (* a ranking-function template (WF, DWF, NWF, Parity — not their [*Flex]
     variants) does not take qualifiers from candidate solutions.  This used to
     compare [FT.kind_of ()] against [Kind.str_of] strings: the flexible
     variants were excluded only because their
     string started with "flexible ", and rewording either side changed
     behaviour silently. *)
  let check_kind (module FT : Template.Function.Type) =
    (not FT.flexible)
    &&
    match FT.kind with
    | Kind.WF | Kind.DWF | Kind.NWF _ | Kind.Parity _ -> true
    | _ -> false

  (* The second level of the failure policy, for one qualifier shape: solve
     the unsat core against a template of that shape and read its solution back
     as qualifiers.  What comes back from the solver is a solution of the
     *qualifier* template, so it is a qualifier and not a candidate solution of
     the problem, whatever the constructor it arrives in is called.

     The shapes are one list of strategies run by this one function, so a
     change that must reach every place that calls [cgen] reaches every
     shape; written out once per shape, nested inside each other's
     [UnsatCore] arm, the copies drift apart. *)
  let learn_quals_from_ucore ~strategy ucores0 vs pvar_labels_map0 =
    let label = strategy.name in
    Debug.print @@ lazy (sprintf "\n*** finding a candidate using [%s]" label);
    match
      Common.PhaseTime.with_phase ("learn/" ^ label) @@ fun () ->
      let inst = fresh_ucore_instance ~ucore:strategy.ask_for_core () in
      csolve ~ucore:strategy.ask_for_core inst
      @@ cgen ~incremental:false ~add_param_cnstrs:(take_param_cnstrs inst)
           ucores0 vs strategy.templates
    with
    | Candidate (learned, certs) ->
        VersionSpace.set_kind_certs vs certs;
        Debug.print
        @@ lazy (sprintf "*** qualifiers learned from unsat core [%s]" label);
        let changed = ref false in
        Map.Poly.iteri template_modules ~f:(fun ~key ~data:(module FT) ->
            if check_kind (module FT) then () (*ToDo*)
            else
              let ref_quals, _ref_terms, _ref_consts =
                Map.Poly.find_exn quals_terms_map key
              in
              match Map.Poly.find learned key with
              | None -> ()
              | Some (_s, t) ->
                  let new_quals =
                    try
                      let phi =
                        let params = FT.params_of () in
                        let uni_senv =
                          Logic.of_old_sort_env_map
                          @@ Map.Poly.of_alist_exn params
                        in
                        Normalizer.normalize @@ Evaluator.simplify
                        @@ Logic.ExtTerm.to_old_formula Map.Poly.empty uni_senv
                             t
                           (*ToDo: t may have non-boolean type*)
                        @@ List.map params ~f:(fst >> Logic.ExtTerm.mk_var)
                      in
                      let quals =
                        if strategy.learn_whole_formula then
                          (* the template's solution as one qualifier, rather
                             than its atoms *)
                          Set.Poly.singleton phi
                        else
                          let pos, neg = Formula.atoms_of phi in
                          let pos = Set.Poly.map ~f:Formula.mk_atom pos in
                          let neg = Set.Poly.map ~f:Formula.mk_atom neg in
                          Set.union pos neg
                      in
                      let quals =
                        if not config.ucore_quals_params_only then quals
                        else params_only_quals ~params:(FT.params_of ()) quals
                      in
                      Set.Poly.map ~f:snd @@ QualifierGenerator.elim_neg
                      @@ Set.Poly.map quals ~f:(fun q -> (FT.params_of (), q))
                    with exn_ when not (Common.Timer.is_async exn_) ->
                      Set.Poly.empty
                  in
                  Debug.print
                  @@ lazy
                       (sprintf "adding qualifiers for %s @ %s:\n%s\n"
                          (Ident.name_of_tvar key) label
                          (String.concat_map_set ~sep:"\n" ~f:Formula.str_of
                             new_quals));
                  let new_quals = Set.diff new_quals !ref_quals in
                  if Set.is_empty new_quals then
                    Debug.print @@ lazy (sprintf "no new qualifier learned\n")
                  else (
                    changed := true;
                    ref_quals := Set.union !ref_quals new_quals));
        if !changed then `Learned (true, Map.Poly.empty)
        else (* ToDo: reachable? *)
          `Learned (false, pvar_labels_map0 (*dummy*))
    | UnsatCore (_ucores, pvar_labels_map) -> `Unsat_core pvar_labels_map

  (* A synthesis round escalates through three levels, and [inner] below is
     that escalation.  Each level is reached only when the one before it
     failed, and each does something the one before it cannot.

     1. Search for a candidate solution over the vocabulary already in hand,
        composing existing qualifiers.  This is the [csolve] on
        [!ref_templates] below; it asks for no new qualifier and can propose
        nothing its qualifiers cannot say.

     2. On failure, learn new qualifiers, by solving the unsat core against a
        template whose target is a *qualifier*.  There are five shapes to try,
        in order, and the first that learns something ends the level:
        [qualifier_learning_strategies] and [learn_quals_from_ucore].  A
        success here enlarges the vocabulary and the round restarts at level 1.

     3. Only if all five fail, grow the structural parameters -- the number of
        disjuncts, of conjuncts, of ranking pieces -- through
        [TemplateUpdateStrategy.update], from the labels the last shape's
        unsat core blamed.  This changes what a candidate can be *shaped* like
        rather than what it can *say*, which is why it is last: no amount of
        shape supplies an atom the vocabulary cannot state.

     The two moves of levels 2 and 3 are monotone but not comparable, so the
     order between them is a search policy rather than a detail.  A round that
     fails at level 3 and is not allowed to yield comes back to level 1 with a
     wider shape, which is the loop this phase has no other exit from. *)
  let rec synthesize num_iters state =
    PCSatCommon.TruthTable.with_valid_budget
      (if config.truth_table_valid_timeout > 0 then
         Some config.truth_table_valid_timeout
       else None)
    @@ fun () -> synthesize_body num_iters state

  and synthesize_body num_iters state =
    (* the spin this counts happens inside one call, so the count is per call *)
    consecutive_failures := 0;
    current_round := num_iters;
    rebuild_after_timeout_only := false;
    let vs = State.version_space_of state in
    let rec inner () =
      (* a strict deadline of an enclosing run has passed: hand control back
         to the loop, whose next phase boundary answers [Timeout] *)
      if PCSatCommon.SolveDeadline.expired_strict () then Yield
      else inner_body ()
    and inner_body () =
      Common.Messenger.receive_request
        (PCSP.Problem.messenger_of APCSP.problem)
        id;
      if !iters_after_updated = 0 then (
        let stamp = Common.Clock.now_float in
        let secs t0 t1 = Time_float.Span.to_sec (Time_float.diff t1 t0) in
        let t0 = stamp () in
        Common.PhaseTime.with_phase "hspaces" (fun () -> update_hspaces vs);
        let t1 = stamp () in
        if Lazy.force CgenProfile.on then
          Stdlib.prerr_endline
          @@ sprintf "[rebuild-profile] hspaces done %.3f" (secs t0 t1);
        ignore @@ reduce_quals_terms vs;
        VersionSpace.initialize_predicates id vs
          (PCSP.Problem.kind_map_of APCSP.problem)
        (*quals_terms_map*);
        let t2 = stamp () in
        Debug.print @@ lazy "**** for non-ucore";
        ref_templates :=
          Common.PhaseTime.with_phase "templates" (fun () ->
              initialize_templates ~ucore:None vs);
        let t3 = stamp () in
        if config.learn_quals_from_ucores then
          Common.PhaseTime.with_phase "ucore-templates" (fun () ->
              List.iter qualifier_learning_strategies ~f:(fun strategy ->
                  Debug.print @@ lazy (sprintf "**** for %s" strategy.name);
                  strategy.templates <-
                    initialize_templates
                      ~ucore:
                        (Some
                           (strategy.shape, strategy.eq_atom, strategy.only_bools))
                      vs));
        if Lazy.force CgenProfile.on then
          Stdlib.prerr_endline
          @@ sprintf
               "[rebuild-profile] hspaces %.3f predicates %.3f templates %.3f \
                ucore_templates %.3f"
               (secs t0 t1) (secs t1 t2) (secs t2 t3) (secs t3 (stamp ()));
        Debug.print @@ lazy "templates generated";
        let reason =
          if !rebuild_after_timeout_only then SynthesisBudget.Timeout_only
          else SynthesisBudget.Other
        in
        rebuild_after_timeout_only := false;
        Common.PhaseTime.with_phase "renew-smt" (fun () ->
            renew_all_smt_instances ~reason ());
        Debug.print @@ lazy "solver initialized");
      let quals_terms_changed =
        !iters_after_updated <> 0
        && reduce_quals_terms vs (*ToDo: always false?*)
      in
      if print_truth_table then
        Hashtbl.Poly.iteri vs.truth_table ~f:(fun ~key ~data ->
            let alist =
              Map.Poly.of_alist_exn
              @@ List.init (TruthTable.length_of_atoms data) ~f:(fun i ->
                  (i, 0))
            in
            let qlist = List.init (TruthTable.length_of_quals data) ~f:Fn.id in
            Debug.print
            @@ lazy ("\n" ^ TruthTable.str_of (key, data) (qlist, alist)));
      if quals_terms_changed then (
        Debug.print @@ lazy "#quals has changed by the qualifier reduction";
        init_incr ();
        inner ())
      else
        match config.restart_threshold with
        | Some threshold when !iters_after_updated >= threshold -> (
            init_incr ();
            Common.PhaseTime.event "synthesis/restart";
            TemplateUpdateStrategy.update template_modules num_iters state None;
            match out_space_of () with [] -> inner () | outs -> OutSpace outs)
        | _ -> (
            if RLCfg.config.enable && RLCfg.config.ask_smt_timeout then (
              RLConfig.lock ();
              Debug.print_stdout
              @@ lazy
                   (sprintf "current timeout: %s"
                   @@
                   match default_smt_instance.smt_timeout with
                   | None -> "null"
                   | Some n -> string_of_int n);
              Out_channel.flush Out_channel.stdout;
              default_smt_instance.smt_timeout <-
                int_of_string_opt @@ In_channel.input_line_exn In_channel.stdin;
              RLConfig.unlock ());
            let diff_sample =
              Set.diff (VersionSpace.examples_of vs) !prev_sample
            in
            (* Level 1: a candidate over the qualifiers already in hand.  It
               asks for an unsat core because a failure here is what levels 2
               and 3 work from. *)
            Debug.print @@ lazy "\n*** finding a candidate using [non-ucore]";
            let arg =
              cgen ~incremental:true
                ~add_param_cnstrs:(take_param_cnstrs default_smt_instance)
                diff_sample vs !ref_templates
            in
            match
              SynthesisBudget.ask_reasking
                ~reask:config.reask_on_timeout_without_rebuild
                ~timeout_only:(function
                  | UnsatCore (ucores, labels) ->
                      !last_query_timed_out && timeout_only_labels ucores labels
                  | Candidate _ -> false)
                ~budget:(fun () -> default_smt_instance.smt_timeout)
                ~expired:PCSatCommon.SolveDeadline.expired_strict
                (fun ~again -> csolve ~ucore:true ~again default_smt_instance arg)
            with
            | Candidate (cand, certs) ->
                VersionSpace.set_kind_certs vs certs;
                iters_after_updated := !iters_after_updated + 1;
                prev_sample := Set.Poly.union_list [ diff_sample; !prev_sample ];
                if
                  let normalize term =
                    let senv, term = Logic.ExtTerm.let_lam term in
                    let senv' =
                      List.mapi senv ~f:(fun i (_, s) ->
                          (Ident.Tvar (sprintf "x%d" (i + 1)), s))
                    in
                    Logic.ExtTerm.mk_lambda senv'
                    @@ Logic.ExtTerm.rename
                         (Map.Poly.of_alist_exn
                         @@ List.map2_exn senv senv' ~f:(fun (x, _) (y, _) ->
                             (x, y)))
                         term
                  in
                  (not @@ Map.Poly.is_empty cand)
                  &&
                  if config.non_progress_up_to_bound_names then
                    PCSatCommon.CandidateEquiv.same_candidates !prev_cand cand
                  else
                    Map.Poly.equal
                      (fun (_, phi1) (_, phi2) ->
                        Stdlib.(normalize phi1 = normalize phi2))
                      !prev_cand cand
                then (
                  (* non progress detecetd *)
                  init_incr ();
                  Common.PhaseTime.event "synthesis/non-progress";
                  TemplateUpdateStrategy.update template_modules num_iters state
                    (Some
                       (Map.Poly.map template_modules ~f:(fun _ ->
                            Set.Poly.singleton Shape)));
                  Debug.print @@ lazy "*** all templates updated";
                  (* and then ask whether any template has left the space it is
                     allowed, exactly as the two other update sites do.  This
                     one is reached when the candidate did not change -- no
                     progress -- and it used to recurse unconditionally, which
                     is what turns "the constraint is unsatisfiable and nothing
                     was learnt" into a loop that grows the template for ever:
                     105 disjuncts over eleven qualifiers in 45 s on one input,
                     141 over 462 rounds on another, with the answer that says
                     the solution is outside the family never reached because
                     the family was grown instead of exhausted.  With no bound
                     stated this still never fires, so nothing changes for a
                     problem that states none. *)
                  match out_space_of () with
                  | [] -> inner ()
                  | outs -> OutSpace outs)
                else (
                  prev_cand := cand;
                  vs.VersionSpace.synthesis_stalled := false;
                  Cands (cand, partial_candidates_of diff_sample vs))
            (*| UnsatCore (_, _) ->
                init_incr ();
                renew_smt_instance default_smt_instance;
                match
                  csolve ~ucore:true default_smt_instance
                  @@ cgen ~incremental:true (VersionSpace.examples_of vs) vs !ref_templates
                with
                | Candidate (cand, certs) ->
                    VersionSpace.set_kind_certs vs certs;
                    (*unreachable?*)
                    iters_after_updated := !iters_after_updated + 1;
                    prev_sample := VersionSpace.examples_of vs;
                    prev_cand := cand;
                    Cands
                      ( cand,
                        partial_candidates_of (VersionSpace.examples_of vs) vs
                      )*)
            | UnsatCore (ucores0, pvar_labels_map0) ->
                init_incr ();
                let quals_changed, pvar_labels_map =
                  if
                    config.learn_quals_from_ucores
                    && (not @@ Set.is_empty ucores0)
                  then
                    (* Level 2: learn new qualifiers, trying each shape in
                         turn and stopping at the first that learns one.  What
                         each shape is and why the last one is different is at
                         [qualifier_learning_strategies]. *)
                    (* Each attempt that comes back with an unsat core has
                       learned which template parameters that core blames, and
                       every one of those is something the search should widen.
                       Keeping only the last attempt's map -- which is what this
                       did, with a [ToDo] saying so -- throws away what the
                       earlier ones found, so the labels are unioned per
                       predicate instead. *)
                    let merge_labels =
                      Map.Poly.merge ~f:(fun ~key:_ -> function
                        | `Left s | `Right s -> Some s
                        | `Both (s1, s2) -> Some (Set.union s1 s2))
                    in
                    (* REACHABLE ON THE DEFAULT PATH. Off -- which is every
                       shipped configuration -- this discards the accumulator
                       and returns the attempt's own map, so [run] threads a
                       value it never reads and the result is the last
                       attempt's map, exactly as before. *)
                    let merge_labels acc m =
                      if config.blame_from_every_qualifier_attempt then
                        merge_labels acc m
                      else m
                    in
                    (* a map that blames something a template module acts
                       on: not empty and not [TimeOut] alone for every
                       predicate *)
                    let informative m =
                      not (timeout_only_labels Set.Poly.empty m)
                    in
                    (* [seen]: the maps returned before, newest first, ending
                       with the candidate search's own *)
                    let rec run acc seen = function
                      | [] -> (false, acc) (* unreachable *)
                      | _ :: _ when PCSatCommon.SolveDeadline.expired_strict () ->
                          (false, acc)
                      | strategy :: rest -> (
                          match
                            learn_quals_from_ucore ~strategy ucores0 vs
                              pvar_labels_map0
                          with
                          | `Learned res -> res
                          | `Unsat_core pvar_labels_map ->
                              let acc = merge_labels acc pvar_labels_map in
                              if List.is_empty rest then (
                                (* every attempt came back with an unsat core: the
                                     given constraint set is likely unsat, but since
                                     parametric examples are used, additional checks
                                     are required to conclude this *)
                                Debug.print
                                @@ lazy
                                     "*** qualifiers not learned from unsat \
                                      core";
                                let blame =
                                  SynthesisBudget.blame_after_learning
                                    ~prefer_informative:
                                      config.widen_from_core_after_learning_timeout
                                    ~informative ~last:acc ~earlier:seen
                                in
                                if not (phys_equal blame acc) then
                                  Common.PhaseTime.event
                                    "synthesis/blame-from-earlier-core";
                                (false, blame))
                              else run acc (pvar_labels_map :: seen) rest)
                    in
                    run pvar_labels_map0 [ pvar_labels_map0 ]
                      qualifier_learning_strategies
                  else (false, pvar_labels_map0)
                in
                let widen_shape () =
                  let t0 = Common.Clock.now_float () in
                  TemplateUpdateStrategy.update template_modules num_iters state
                    (Some pvar_labels_map);
                  if Lazy.force CgenProfile.on then
                    Stdlib.prerr_endline
                    @@ sprintf "[rebuild-profile] widen %.3f"
                         (Time_float.Span.to_sec
                            (Time_float.diff (Common.Clock.now_float ()) t0));
                  Debug.print @@ lazy "*** all templates updated";
                  match config.sync_threshold with
                  | None -> ()
                  | Some thre ->
                      Map.Poly.iter template_modules ~f:(fun (module FT) ->
                          FT.sync thre)
                in
                if quals_changed then (
                  Common.PhaseTime.event "synthesis/learned";
                  consecutive_failures := 0;
                  (* The two moves are NOT symmetric, which is why their order is
                     not a thing that can simply be swapped: learning reports
                     whether it changed anything, and this branch is where it
                     did, whereas growing the shape is unconditional and has no
                     failure outcome except leaving a bound that is unset by
                     default.  So the policy that spends the whole vocabulary
                     budget before the first structural step is not one of two
                     orders but the only one the asymmetry admits -- unless the
                     shape is grown here as well, which is what this does.
                     Measured on a corpus where learning fires 21 times against
                     4 failures on one file and 5 against 86 on another: tying
                     the structural budget to learning's failures hands those
                     two files wildly different budgets, and this does not. *)
                  if config.widen_shape_with_learning then widen_shape ();
                  match out_space_of () with
                  | [] -> inner ()
                  | outs -> OutSpace outs)
                else (
                  consecutive_failures := !consecutive_failures + 1;
                  match config.yield_after_failures with
                  | Some n when !consecutive_failures >= n ->
                      Debug.print
                      @@ lazy
                           (sprintf
                              "*** yielding after %d rounds that fitted nothing"
                              !consecutive_failures);
                      consecutive_failures := 0;
                      (* tell the phases after this one that the loop is not
                         going to synthesise its way out, so that a mechanism
                         which earns its cost only here can switch itself on *)
                      vs.VersionSpace.synthesis_stalled := true;
                      Yield
                  | _ ->
                  (* Level 3: no shape learned a qualifier, so grow the
                     structural parameters from what the last shape's core
                     blamed. *)
                  (* A failure that is only a synthesis timeout -- no core,
                     every predicate labelled [TimeOut] -- leaves the shape as
                     it was, so the rebuild it leads to may keep the doubled
                     budget (see [renew_smt_instance]). *)
                  rebuild_after_timeout_only :=
                    timeout_only_labels ucores0 pvar_labels_map0;
                  widen_shape ();
                  match out_space_of () with
                  | [] -> inner ()
                  | outs -> OutSpace outs))
    in
    (* The probe returns before the solver sees this round's examples, and it
       leaves [prev_sample] alone, so the incremental constraint generation
       adds them in the next round exactly as if this round had not happened.
       It leaves [prev_cand] alone too: the non-progress test compares two
       template answers, and the probe is not one. *)
    let senv = PCSP.Problem.senv_of APCSP.problem in
    if
      config.false_probe_on_negative_examples && (not !false_probe_done)
      && FalseProbe.applies
           ~kind_map:(PCSP.Problem.kind_map_of APCSP.problem)
           ~senv (VersionSpace.examples_of vs)
    then (
      false_probe_done := true;
      Debug.print
      @@ lazy
           "\n\
            *** no example asks a predicate to hold: proposing false for \
            every predicate";
      vs.VersionSpace.synthesis_stalled := false;
      Cands (FalseProbe.candidate senv, []))
    else inner ()
end
