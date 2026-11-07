open Core
open Common.Ext
open Ast
open Ast.Logic

type t

(* A counterexample of PPDP 2009's procedure (Unno and Kobayashi,
   "Dependent Type Inference with Interpolants"): the unsatisfiable system
   unfolded along one derivation.  Each node is a clause instance: its head
   and body applications and its formula part, with the clause's variables
   renamed to the instance's own; a node's [i]-th child is the instance
   whose head derives the node's [i]-th body application, the two argument
   lists equal under [model].  [model] gives every variable of the
   derivation a value under which every instance holds, so no assignment of
   relations to the predicates satisfies the clauses ([counterexample_holds]
   checks it by evaluation).  [condition] is the refuted goal's body under
   the least solution, projected onto [vocabulary] (the goal's own
   variables, or those asked for); [model] restricted to [vocabulary]
   satisfies it.  [expansion] names the unfolding that was refuted. *)
type cex_node = {
  head : (Ident.pvar * LogicOld.Term.t list) option;
  body : (Ident.pvar * LogicOld.Term.t list) list;
  constr : LogicOld.Formula.t;
  sources : string list;
      (** where the clause was generated, when its producer recorded it *)
  children : cex_node list;
}

type counterexample = {
  condition : LogicOld.Formula.t;
  vocabulary : LogicOld.sort_env_list;
  model : (LogicOld.sort_bind * LogicOld.Term.t) list;
  derivation : cex_node;
  expansion : string;
}

type refutation =
  | Formula of LogicOld.Formula.t
  | Proof of Refutation.t
  | External of string
  | Counterexample of counterexample
      (** PPDP 2009's counterexample: a derivation and its model *)

type solution =
  | Sat of term_subst_map
  | Unsat of refutation option
      (** the evidence, when the solver keeps any: a formula (SPACER's ground
          derivation, which MuStrat reads as a counter-strategy), a recorded
          refutation (PCSat), or a backend's reason *)
  | Unknown
  | OutSpace of Ident.tvar list
  | Timeout

type oracle = CandSolOld.t option

val lts_str_of_solution : solution -> string

val counterexample_holds : counterexample -> bool
(** every instance of the derivation holds under the model, by evaluation,
    and the root is a goal *)

val str_of_counterexample : counterexample -> string list


type bounds = (Ident.tvar, int * (sort_env_map * term)) Map.Poly.t

(** [GroundSeeds]' payload: each seed is a binder's name and its values;
    each atom a predicate's name and a value (or nothing) per argument, an
    application the seeds make ground where the binders' names are lost;
    [choice_values] are the values of every other integer variable;
    [atom_budget] and [max_combos] bound the instances the receiver builds;
    [trace] asks the receiver for a stderr line per seed message and per
    refutation holding seeded examples; [synthesis_reads] says whether the
    receiver's template synthesis reads the instances and what is derived
    from them (when false only resolution and labeling do);
    [refutation_cone] says whether the receiver keeps only the instances a
    labeling refutation of the message's instances can use;
    [stop_after_fruitless] ([Some k]) asks the receiver to unfold no further
    message once [k] consecutive messages kept no instance *)
type ground_seeds = {
  seeds : (string * Ast.Value.t list) list;
  atoms : (string * Ast.Value.t option list) list;
  choice_values : Ast.Value.t list;
  atom_budget : int;
  max_combos : int;
  trace : bool;
  synthesis_reads : bool;
  refutation_cone : bool;
  stop_after_fruitless : int option;
}

type Common.Messenger.info +=
  | CandidateSolution of
      (term_subst_map
      * term_subst_map
      * ClauseSet.t
      * ClauseSet.t
      * (sort_env_map * LogicOld.FunEnv.t * (Ident.tvar, term) Hashtbl.Poly.t)
        option)
  | LowerBounds of bounds
  | UpperBounds of bounds
  | GroundSeeds of ground_seeds
      (** values for some of the problem's variables, named by the binders
          they came from: the receiver may hold ground instances of its own
          clauses at those values as examples, and nothing else *)

module type ProblemType = sig
  val problem : t
end

val of_formulas : ?params:Params.t -> (sort_env_map * term) Set.Poly.t -> t

val of_old_formulas :
  ?params:Params.t ->
  (LogicOld.sort_env_map * LogicOld.Formula.t) Set.Poly.t ->
  t

val of_clauses : ?params:Params.t -> Clause.t Set.Poly.t -> t
val to_nnf : t -> t

(* add to each clause the instances, at the terms it hands its unknowns, of the
   premises it states with a quantifier; an instance is a consequence of the
   premise, so the clause is left equivalent *)

val alpha_canonical_key : LogicOld.Formula.t -> string
(** a printed key: equal keys only for alpha-equivalent formulas; equal keys
    for formulas that differ only in the names of their quantifier, [let] and
    recursive-definition argument binders *)

val dedup_alpha_equivalent_disjuncts : ?print:(string lazy_t -> unit) -> t -> t
(** Drop disjuncts of a clause that are the same formula once their bound
    variable names are ignored. Merging clauses copies a shared premise once per
    clause and each copy carries its own binder names, so a clause can hold many
    alpha-equivalent copies of one premise; a disjunction is unchanged by
    removing them. Runs before any pass that expands a quantifier, so that the
    copies are not expanded as well. A problem stating no quantifier is returned
    untouched without a walk. *)

val dedup_alpha_equivalent_clauses : t -> t * int
(** [(p', n)]: [p] in clausal form without the [n] clauses that print, with
    their sort environments, as an earlier clause does once the binders of
    their formulas are renamed; exact, since a repeated conjunct changes no
    constraint set. A [Raw] problem, or one with no such clause, is returned as
    it is with [n = 0]; the stable clauses are not touched. *)

val instantiate_quantified_premises : ?max_instances:int -> t -> t
val to_cnf : t -> t
val params_of : t -> Params.t
val stable_clauses_of : t -> ClauseSet.t
(** Raises unless the problem is in CNF, which holds after [to_cnf] and [make]
    but not straight out of a reader; [clauses_of_opt] is the total form. *)
val clauses_of : ?full_clauses:bool -> t -> ClauseSet.t

val clauses_of_opt : ?full_clauses:bool -> t -> ClauseSet.t option
val formulas_of : ?full_clauses:bool -> t -> (sort_env_map * term) Set.Poly.t
val formula_of : ?full_clauses:bool -> t -> sort_env_map * term
val old_formulas_of : ?full_clauses:bool -> t -> LogicOld.Formula.t Set.Poly.t
val old_formula_of : ?full_clauses:bool -> t -> LogicOld.Formula.t
val senv_of : t -> sort_env_map
val kind_map_of : t -> Kind.map
val kind_of : t -> Ident.tvar -> Kind.t
val dtenv_of : t -> LogicOld.DTEnv.t
val fenv_of : t -> LogicOld.FunEnv.t
val sol_space_of : t -> SolSpace.t
val messenger_of : t -> Common.Messenger.t option
val sol_for_eliminated_of : t -> term_subst_map

val elimination_reasons_of :
  t -> (Ident.tvar, Params.elim_reason * int) Map.Poly.t

val sol_for_resolved_of : t -> (Ident.tvar, Logic.term Lazy.t) Map.Poly.t

val erasure_trail_of :
  t -> (Ident.pvar, ([ `RAF | `FAR ] * int list) list) Map.Poly.t

val args_record_of : t -> (Ident.pvar, bool array * Sort.t list) Map.Poly.t

val partial_sol_targets_of :
  t -> (Ident.tvar, Params.random_info Set.Poly.t) Map.Poly.t

val dep_graph_of : t -> (Ident.tvar, Ident.tvar_set) Map.Poly.t
val fnpvs_senv_of : t -> sort_env_map

val single_valued_pvs_of : t -> (Ident.tvar, Sort.t * int) Map.Poly.t
(** Every predicate single-valued at a known argument position, with that
    position: [FN] at its last, [Uniq (j, _)] at [j]. *)

val totpvs_senv_of : t -> sort_env_map

(** each total predicate with its universally quantified positions *)
val tot_positions_of : t -> (Ident.tvar, int list) Map.Poly.t
val wfpvs_senv_of : t -> sort_env_map
val dwfpvs_senv_of : t -> sort_env_map

val nwfpvs_senv_of :
  t ->
  ( Ident.tvar,
    Ident.tvar
    * Sort.t list
    * Ident.tvar
    * Sort.t list
    * Ident.tvar
    * Sort.t list )
  Map.Poly.t

val paritypvs_senv_of :
  t ->
  ( Ident.tvar,
    Kind.nwf * Ident.tvar * Sort.t list * Ident.tvar * Sort.t list )
  Map.Poly.t

val default_solution_of_unused :
  Params.t -> Ident.tvar -> Logic.Sort.t -> Logic.term option

(* the predicates whose kind an engine that reads only the clauses cannot honour,
   each with its kind: every kind but [Ord] states an obligation the clauses do
   not carry *)
val non_ord_kinds_of : t -> (Ident.tvar * Kind.t) list
val fnpvs_of : t -> Ident.tvar_set
val uniqpvs_of : t -> Ident.tvar_set
val totpvs_of : t -> Ident.tvar_set
val wfpvs_of : t -> Ident.tvar_set
val dwfpvs_of : t -> Ident.tvar_set
val nwfpvs_of : t -> Ident.tvar_set
val paritypvs_of : t -> Ident.tvar_set
val admpvs_of : t -> Ident.tvar_set
val integpvs_of : t -> Ident.tvar_set
val num_constrs : t -> int
val num_pvars : t -> int

(* all non-predicate function variables *)
val npfvs_of : t -> Ident.tvar_set

(* all predicate variables including well-founded, functional, and non-empty ones *)
val pvs_of : t -> Ident.tvar_set
(** an ordinary predicate that is also bool-valued, which is what every caller
    of it wants and what the old name [is_ord_pred] did not say: it names the
    kind while conjoining a test on the return sort, and every [is_*_pred]
    beside it is the kind alone *)
val is_bool_valued_ord_pred : t -> Ident.tvar -> bool

(** the kind alone *)
val is_ord_kind : t -> Ident.tvar -> bool

(** the return sort alone.  An unknown of kind [Ord] returning anything but
    [bool] is not a predicate and has no template -- an SMT-LIB
    [declare-const] of a bit-vector sort read as a constrained Horn problem is
    one *)
val is_bool_valued : t -> Ident.tvar -> bool
val is_fn_pred : t -> Ident.tvar -> bool
val is_uniq_pred : t -> Ident.tvar -> bool
val is_tot_pred : t -> Ident.tvar -> bool
val is_wf_pred : t -> Ident.tvar -> bool
val is_dwf_pred : t -> Ident.tvar -> bool
val is_nwf_pred : t -> Ident.tvar -> bool
val is_parity_pred : t -> Ident.tvar -> bool
val is_adm_pred : t -> Ident.tvar -> bool
val is_adm_pred_with_cond : t -> Ident.tvar -> bool
val adm_of : t -> Ident.tvar -> Kind.adm option
val is_integ_pred : t -> Ident.tvar -> bool
val is_int_fun : t -> Ident.tvar -> bool

(** kind [RealFun] and a [Real] return sort, as [is_int_fun] is for [Int] *)
val is_real_fun : t -> Ident.tvar -> bool

val is_regex : t -> Ident.tvar -> bool
(** the synthesizer has no template for an unknown of this kind at this sort --
    an SMT-LIB [declare-const] of a bit-vector or integer sort read as a
    constrained Horn problem is one, the unknown being an ordinary predicate
    that does not return [bool].  Its own name because it is an unsupported
    INPUT rather than an internal error: the caller reports [unknown], which is
    an ordinary answer, where a [failwith] reaches the user as a backtrace and a
    corpus sweep as a crash *)
exception NoTemplate of string

(** [refuse_non_ord_kinds ~backend pcsp] raises [NoTemplate] when [pcsp] carries
    a predicate whose kind [backend] cannot honour, naming them.  It raises the
    unsupported-input exception rather than failing, so that the caller reports
    an ordinary [unknown]: a refusal delivered as a backtrace with nothing on
    the verdict stream is read by every harness here as the tool crashing. *)
val refuse_non_ord_kinds : backend:string -> t -> unit

val is_raw : t -> bool
val is_cnf : t -> bool

(* [_exn]: these two *refuse* a problem that has already been clausified, and
   the refusal is an exception rather than a verdict.  [map_if_raw] below is the
   one whose name promises what it does, returning a clausified problem
   unchanged. *)
val map_raw_old_exn :
  f:
    ((LogicOld.sort_env_map * LogicOld.Formula.t) Set.Poly.t ->
    (LogicOld.sort_env_map * LogicOld.Formula.t) Set.Poly.t) ->
  t ->
  t

val map_raw_exn :
  f:((sort_env_map * term) Set.Poly.t -> (sort_env_map * term) Set.Poly.t) ->
  t ->
  t

val map_if_raw :
  f:((sort_env_map * term) Set.Poly.t -> (sort_env_map * term) Set.Poly.t) ->
  t ->
  t

val map_old :
  f:
    (LogicOld.sort_env_map * LogicOld.Formula.t ->
    LogicOld.sort_env_map * LogicOld.Formula.t) ->
  t ->
  t

(** [map_old] on the formulas [touch] holds of, the identity on the others
    (no round trip); equal to [map_old ~f] when [f]'s round trip leaves every
    rejected formula unchanged. *)
val map_old_where :
  touch:(sort_env_map * term -> bool) ->
  f:
    (LogicOld.sort_env_map * LogicOld.Formula.t ->
    LogicOld.sort_env_map * LogicOld.Formula.t) ->
  t ->
  t

(** [map_old] for an [f] that returns [None] on a formula it leaves as it is:
    such a formula is kept without a round trip, and the problem itself is
    returned when [f] changes nothing. *)
val map_old_changed :
  f:
    (LogicOld.sort_env_map * LogicOld.Formula.t ->
    (LogicOld.sort_env_map * LogicOld.Formula.t) option) ->
  t ->
  t

val concat_map_old :
  f:
    (LogicOld.sort_env_map * LogicOld.Formula.t ->
    (LogicOld.sort_env_map * LogicOld.Formula.t) Set.Poly.t) ->
  t ->
  t

val map : f:(sort_env_map * term -> sort_env_map * term) -> t -> t

val concat_map :
  f:(sort_env_map * term -> (sort_env_map * term) Set.Poly.t) -> t -> t

(*val str_of_pvars: pvars -> string
  val str_of_clause : clause -> string *)
val str_of : t -> string

(*val str_of_senv : t -> string*)
val str_of_info : t -> string
val str_of_solution : solution -> string
val str_of_sol_with_witness : solution -> string
val str_of_sygus_solution :
  ?signature:SyGuS.Printer.signature -> solution -> string
(** the answer in the SyGuS output format; with the [signature] of a SyGuS
    input, a [Sat] answer defines exactly the functions it requests, or is
    the format's line for no answer *)
val to_yojson : t -> Yojson.Safe.t
val add_non_emptiness : LogicOld.pred_bind -> t -> t
val add_formula : sort_env_map * term -> t -> t
val add_formulas : (sort_env_map * term) Set.Poly.t -> t -> t
val add_clause : Clause.t -> t -> t
val add_clauses : ClauseSet.t -> t -> t
val divide : t -> t list
val merge_sols : t -> solution list -> solution
val extend_sol : solution -> term_subst_map -> solution
(*val nest_subst : term_subst_map -> term_subst_map*)

val id_of : t -> int option
val ast_size_of : t -> int

val nwf_tag_of :
  t -> Ident.tvar -> (Kind.nwf * (Ident.tvar * Ident.tvar)) option

val instantiate_svars_to_int : t -> t
val elim_ite : t -> t
val elim_ite_quant : t -> t
val normalize : t -> t
val of_sygus : SyGuS.Problem.Make(SyGuS.Problem.ExtTerm).t -> t
val of_lts : LTS.Problem.t -> t
val share_unused_params_fvs : bool Atomic.t
val triv_fn_linear : bool Atomic.t
(** when set, [remove_unused_params] reads a raw problem's free variables
    with [Logic.Term.fvs_within], kept to the parameters' names, deciding the
    same membership *)

val remove_unused_params : t -> t
val decompose_uniq : t -> t
(** Each [Uniq (j, _)] predicate replaced by an ordinary domain predicate and
    an [FN] predicate at position [j]; equisatisfiable, the definition recorded
    for the final answer. *)

val relativise_prop_positions : t -> t
(** Every clause with an admissible or integrable unknown given the premise
    [0 <= t] for each real component [t] of each such application's last
    argument, the answer value whose source domain is the non-negative reals:
    the negative instances a [Real]-sorted position would otherwise demand are
    removed, the solution space is untouched, and no solution is lost.  The
    identity on a problem without such an unknown. *)

val prop_components_of_app : (Ident.tvar, Sort.t) Map.Poly.t -> term -> term list
(** The real components of the answer argument of an application of an
    unknown in the given map (from each admissible or integrable unknown to
    the sort of its last argument), empty for any other atom. *)

val prop_position_violations : t -> Ident.tvar_set
(** The variables that occur, in one constraint, both in the answer argument
    of an admissible or integrable application and in a non-answer argument of
    one; empty when the kinded positions are sort-separated. *)

val prop_sorts_of : t -> (Ident.tvar, Sort.t) Map.Poly.t
(** Each admissible or integrable unknown with the sort of its answer
    position, its last argument. *)

val encode_head_disjunctions : t -> t
(** A disjunctive head replaced by a skolemised choice witness of kind [FN];
    equisatisfiable.  For measuring the encoding against the disjunction. *)

val update_params : t -> Params.t -> t
val map_params : f:(Params.t -> Params.t) -> t -> t
val update_params_dtenv : t -> t

(** [Params.fenv] restricted to the definitions the constraints reach
    (transitively through bodies and recorded properties) and the size
    functions; the problem itself when nothing is dropped *)
(** The functions a reconstruction pass added to the environment as
    vocabulary; [prune_unreached_definitions] keeps them although no clause
    applies them.  Written before solving only. *)
val reconstructed_functions : Ident.tvar Set.Poly.t Atomic.t

(** The environment's functions a reconstruction pass found equal to one it
    reconstructed (PCSat's [reuse_equal_functions]): read by the bounded
    reconstructed-function vocabulary and kept by
    [prune_unreached_definitions] like the names above, but never removed
    from the hypothesis space.  Written before solving only. *)
val reconstruction_aliases : Ident.tvar Set.Poly.t Atomic.t

val prune_unreached_definitions : t -> t

(** [known_functions_read_by_constraints ~applied_only fenv pcsp]: the names
    of [fenv] that a constraint of [pcsp] (stable clauses included) reads
    where no unknown, universal variable or binder shadows them, and with
    [~applied_only:true] only those it applies to an argument.  Read on the
    constraints as they are, never through the process-global function
    environment, so it holds for a caller that restored that environment. *)
val known_functions_read_by_constraints :
  applied_only:bool -> Ast.LogicOld.FunEnv.t -> t -> Ast.Ident.tvar Set.Poly.t
val set_params_sol_space : t -> SolSpace.t -> t
val normalize_uni_senv : t -> t

val recover_elimed_params_of_sol :
  (Ident.pvar, bool array * Sort.t list) Map.Poly.t ->
  term_subst_map ->
  term_subst_map

val sol_of_candidate : t -> CandSol.t -> term_subst_map
val subst_formula : term_subst_map -> term -> term
(** [subst_formula sub phi] is what [subst] does to each constraint: [phi]
    itself when no variable of [sub] is free in it, and otherwise
    [Logic.Term.subst sub phi] up to the names of bound variables (where
    [phi] and [sub]'s range are beta-normal; beta-equivalent otherwise). *)

val subst : ?bpvs:Ident.tvar_set -> ?elim:bool -> term_subst_map -> t -> t
val cochc_subst_of : t -> term_subst_map
(** The substitution [cochc_to_chc] applies: each [Ord] predicate to its
    complement. *)

val cochc_to_chc : t -> t
val elim_unsat_wf_predicates : print:(string lazy_t -> unit) -> t -> t
val elim_unsat_nwf_predicates : print:(string lazy_t -> unit) -> t -> t
val elim_unsat_parity_predicates : print:(string lazy_t -> unit) -> t -> t
val elim_triv_nwf_predicate : t -> t
val elim_triv_parity_predicate : t -> t
val elim_triv_fn_predicate : t -> t

val elim_fn_feeding_fn_predicate : t -> t

val restore_witness_universals : t -> t
(** replaces the clauses of a functional witness whose result only reaches
    the clauses' pure parts by one clause with the quantifier restored;
    equivalent (the argument is at the definition) *)
(** drops a functional body atom whose result only feeds the inputs of
    other functional atoms applied once each, which also take its inputs;
    equisatisfiable in both directions (the argument is at the definition) *)
val merge_clauses : t -> t

val is_qualified_partial_solution :
  print:(string lazy_t -> unit) ->
  Ident.tvar_set ->
  Ident.tvar_set ->
  ClauseSet.t ->
  bool

val check_valid : (sort_env_map -> term -> bool) -> t -> term_subst_map -> bool

val make :
  ?skolem_pred:bool ->
  ?prefix:string option ->
  LogicOld.Formula.t list ->
  SMT.Problem.envs ->
  t

module V : sig
  type t = Ident.tvar option

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end

module G : Graph.Sig.G

val dep_graph_of_chc : t -> G.t (* only for CHCs *)
val output_graph : Stdlib.out_channel -> G.t -> unit
val str_of_graph : G.t -> string

(** on unless a caller switches it off: the one-point rule through
    constructor applications, applied to an existential with an unknown under
    it before [make] skolemises it *)
val onepoint_constructor_binders : bool ref

(** exact in every model; exposed for its test *)
val elim_constructor_points : Ast.LogicOld.Formula.t -> Ast.LogicOld.Formula.t

(** [solve_constructor_point x lhs rhs]: when [rhs] holds [x] along one path
    of constructor applications of inductive datatypes and [lhs] does not hold
    [x], [Some (s, guards)] with [lhs = rhs] equivalent, in every model of the
    background theory, to [x = s /\ guards]; neither [s] nor a guard holds
    [x] *)
val solve_constructor_point :
  Ast.Ident.tvar ->
  Ast.LogicOld.Term.t ->
  Ast.LogicOld.Term.t ->
  (Ast.LogicOld.Term.t * Ast.LogicOld.Formula.t list) option

(** off unless a caller switches it on: a witness [make] skolemises takes only
    the universals its existential's body mentions (and the universal functions
    a dependency set can name), not every universal in scope *)
val skolem_body_variables_only : bool ref
