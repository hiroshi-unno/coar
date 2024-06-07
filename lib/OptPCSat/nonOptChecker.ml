open Ast.Ident
open Ast.Logic

module type NonOptCheckerType = sig
  val improve :
    sort_env_map -> tvar list -> term_subst_map -> term * sort_env_map

  val gen_maxc : sort_env_map -> tvar -> term_subst_map -> sort_env_map * term
  val is_dup : tvar -> bool
  val is_ddown : tvar -> bool
end
