open Ast
open Ast.LogicOld

type t = {
  kind : Predicate.fixpoint;
  name : Ident.pvar;
  args : sort_env_list;
  body : Formula.t;
}

val make : Predicate.fixpoint -> Ident.pvar -> sort_env_list -> Formula.t -> t
val map : (Formula.t -> Formula.t) -> t -> t
val map_list : (Formula.t -> Formula.t) -> t list -> t list
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
