open Ast
open Ast.LogicOld

type t = Predicate.fixpoint * Ident.pvar * sort_env_list * Formula.t

val make : Predicate.fixpoint -> Ident.pvar -> sort_env_list -> Formula.t -> t
val map : (Formula.t -> Formula.t) -> t -> t
val map_list : (Formula.t -> Formula.t) -> t list -> t list
val let_ : t -> Predicate.fixpoint * Ident.pvar * sort_env_list * Formula.t
val fixpoint_of : t -> Predicate.fixpoint
val pvar_of : t -> Ident.pvar
val args_of : t -> sort_env_list
val body_of : t -> Formula.t
val pvars_of_list : t list -> Ident.pvar list
val pred_sort_env_of_list : t list -> pred_sort_env_set
val pred_sort_env_map_of_list : pred_sort_env_map -> t list -> pred_sort_env_map
val sort_env_of_list : t list -> Logic.sort_env_set
val subst : TermSubst.t -> t -> t

val lookup :
  t list ->
  Ident.pvar ->
  (Predicate.fixpoint * sort_env_list * Formula.t) option

val to_formula : t -> Formula.t
val str_of : t -> string
val str_of_ : t -> string
val str_of_list : t list -> string
val pr_list : Format.formatter -> t list -> unit
val replace_app_add : Formula.t -> Term.t -> Sort.t -> Formula.t
val elim_mu_with_rec : t list -> Ident.tvar -> t list
