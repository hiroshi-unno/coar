open Core
open Ast
open Ast.LogicOld

type query = Formula.t
type t = { preds : Pred.t list; query : query }
type solution = Valid | Invalid | Unknown | Timeout

val make : Pred.t list -> query -> t
val flip_solution : solution -> solution
val str_of_solution : solution -> string
val lts_str_of_solution : solution -> string
val preds_of : t -> Pred.t list
val query_of : t -> query
val size_of : t -> int
val penv_of : ?init:pred_sort_env_map -> t -> pred_sort_env_map
val let_muclp : t -> Pred.t list * query
val get_depth_ht : t -> (Ident.pvar, int) Hashtbl.Poly.t
val avoid_dup : Ident.pvar -> Ident.pvar list -> Ident.pvar
val of_formula : Formula.t -> t
val to_formula : t -> Formula.t
val str_of : t -> string
val has_only_mu : t -> bool
val has_only_nu : t -> bool
val has_only_forall : t -> bool
val has_only_exists : t -> bool
val has_no_quantifier : t -> bool
val bind_fvs_with_forall : t -> t
val map_formula : (Formula.t -> Formula.t) -> t -> t
val aconv_tvar : t -> t
val move_quantifiers_to_front : t -> t
val rm_forall : t -> t
val complete_tsort : t -> t
val complete_psort : pred_sort_env_map -> t -> t
val simplify : t -> t
val get_dual : t -> t
val get_greatest_approx : t -> t
val typeinf : print:(string lazy_t -> unit) -> t -> t
val of_chc : ?only_pos:bool -> PCSP.Problem.t -> t

val of_lts :
  ?live_vars:(string -> sort_env_set) option ->
  ?cut_points:string Set.Poly.t option ->
  LTS.Problem.t ->
  t

val check_problem : t -> t
