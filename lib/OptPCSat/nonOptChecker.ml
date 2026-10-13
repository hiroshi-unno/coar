(* The interface of an improver: [improve] builds the constraint that a
   solution strictly better than the current one exists (with the
   non-emptiness predicates it introduces), and [gen_maxc] the constraint
   that keeps an already optimized predicate at least as good as it is. *)
open Ast.Ident
open Ast.Logic

module type NonOptCheckerType = sig
  val improve :
    sort_env_map -> tvar list -> term_subst_map -> term * sort_env_map

  val gen_maxc : sort_env_map -> tvar -> term_subst_map -> sort_env_map * term
  val is_dup : tvar -> bool
  val is_ddown : tvar -> bool
end
