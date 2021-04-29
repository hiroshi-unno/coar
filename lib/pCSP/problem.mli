open Core
open Ast
open Ast.Logic

type t

type solution = Sat of (Ident.tvar, term) Map.Poly.t | Unsat | Unknown

exception Timeout

module type ProblemType = sig val problem : t end

val of_formulas : ?params:Params.t -> (SortMap.t * term) Set.Poly.t -> t
val of_clauses : ?params:Params.t -> Clause.t Set.Poly.t -> t

val to_nnf : t -> t
val to_cnf : t -> t

val clauses_of : t -> ClauseSet.t
val formulas_of : t -> (SortMap.t * term) Set.Poly.t
val formula_of : t -> term
val params_of : t -> Params.t
val senv_of : t -> SortMap.t
val dtenv_of : t -> LogicOld.DTEnv.t
val fenv_of :t -> (Ident.tvar * (Ident.tvar * LogicOld.Sort.t) list * LogicOld.Sort.t * LogicOld.Term.t * (LogicOld.Formula.t Set.Poly.t)) Set.Poly.t
val wfpvs_senv_of : t -> SortMap.t
val fnpvs_senv_of : t -> SortMap.t
val wfpvs_of : t -> Ident.tvar Set.Poly.t
val fnpvs_of : t -> Ident.tvar Set.Poly.t

(** all non-predicate function variables *)
val npfvs_of : t -> Ident.tvar Set.Poly.t

(** all predicate variables including wf and fn predicate variables *)
val pvs_of : t -> Ident.tvar Set.Poly.t

val is_wf_pred : t -> Ast.Ident.tvar -> bool
val is_fn_pred : t -> Ast.Ident.tvar -> bool
val is_ord_pred : t -> Ast.Ident.tvar -> bool
val is_int_fun : t -> Ast.Ident.tvar -> bool

val map_if_raw_old : f:((LogicOld.SortMap.t * LogicOld.Formula.t) Set.Poly.t -> (LogicOld.SortMap.t * LogicOld.Formula.t) Set.Poly.t) -> t -> t
val map_if_raw : f:((SortMap.t * term) Set.Poly.t -> (SortMap.t * term) Set.Poly.t) -> t -> t

(*val str_of_pvars: pvars -> string
  val str_of_clause : clause -> string *)
val str_of : t -> string
val str_of_info : t -> string
val str_of_solution : solution -> string
val str_of_sygus_solution : solution -> string

val add_non_emptiness : (Ident.pvar * LogicOld.Sort.t list) -> t -> t
val add_formula : (SortMap.t * term) -> t -> t
val add_clause : Clause.t -> t -> t
val divide : t -> t list
val merge_sol : t -> (solution * int) list -> solution * int
val extend_sol : solution -> (Ident.tvar, term) Map.Poly.t -> solution

val of_sygus: SyGuS.Problem.Make(SyGuS.Problem.ExtTerm).t -> t
val of_lts: LTS.Problem.t -> t

val remove_unused_params : t -> t

val update_params_dtenv : t -> t
