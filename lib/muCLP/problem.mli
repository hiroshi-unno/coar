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
val str_of : t -> string
val has_only_mu : t -> bool
val has_only_nu : t -> bool
val has_only_forall : t -> bool
val has_only_exists : t -> bool
val has_no_quantifier : t -> bool
val map_formula : (Formula.t -> Formula.t) -> t -> t
val size_of : t -> int
val penv_of : ?init:pred_sort_env_map -> t -> pred_sort_env_map
val get_depth_ht : t -> (Ident.pvar, int) Hashtbl.Poly.t
val avoid_dup : Ident.pvar -> Ident.pvar list -> Ident.pvar
val bind_fvs_with_forall : t -> t
val aconv_tvar : t -> t
val move_quantifiers_to_front : t -> t
val rm_forall : t -> t
val simplify : t -> t
val complete_tsort : t -> t
val complete_psort : pred_sort_env_map -> t -> t
val check_problem : t -> t
