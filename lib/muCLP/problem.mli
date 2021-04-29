
(*
  entrypoint should be of the form:
    Forall ... Forall <formula>
  <formula> and t's formula don't contain nu, mu predicates
  A body of func should not have negative occurence of predicate application.
  It doesn't matter even if func list does not have order unlike the definition in POPL '17.
*)
open Core
open Ast
open Ast.LogicOld

type entrypoint = Formula.t
type func = Predicate.fixpoint * Ident.pvar * SortEnv.t * Formula.t
type t = MuCLP of func list * entrypoint
type solution = Valid | Invalid | Unknown

exception Timeout

val make: func list -> entrypoint -> t
val mk_func: Predicate.fixpoint -> Ident.pvar -> SortEnv.t -> Formula.t -> func

val flip_solution: solution -> solution
val str_of_solution: solution -> string

val get_functions: t -> func list
val get_entrypoint: t -> entrypoint
val get_fixpoint_of_function: func -> Predicate.fixpoint
val get_pvar_of_function: func -> Ident.pvar
val get_args_of_function: func -> SortEnv.t
val get_body_of_function: func -> Formula.t
val get_size: t -> int

val let_muclp: t -> func list * entrypoint
val let_function: func -> Predicate.fixpoint * Ident.pvar * SortEnv.t * Formula.t

val avoid_dup: Ident.pvar -> Ident.pvar list -> Ident.pvar

val of_formula: Formula.t -> t
val to_formula: t -> Formula.t

val str_of_func: func -> string
val str_of: t -> string

val is_onlymu: t -> bool
val is_onlynu: t -> bool
val is_onlyforall: t -> bool
val is_onlyexists: t -> bool
val is_noquantifier: t -> bool

val aconv_tvar: t -> t
val move_quantifiers_to_front: t -> t
val rm_forall: t -> t
val complete_tsort: t -> t
val complete_psort: (Ident.pvar, Sort.t list) Map.Poly.t -> t -> t

val simplify: t -> t
val get_dual: t -> t
val get_greatest_approx: t -> t

val of_lts:
  ?live_vars:(string -> (Ident.tvar * Sort.t) Set.Poly.t) option ->
  ?cut_points:(string Set.Poly.t) option -> LTS.Problem.t -> t

val replace_app: (Formula.t -> Formula.t) -> Formula.t -> Formula.t
val replace_app_add: Formula.t -> Term.t -> Sort.t -> Formula.t
val elim_mu_from_funcs_with_rec: func list -> Ast.Ident.tvar -> func list
val get_next_funcs: Formula.t -> Ast.Ident.pvar list

val of_chc: PCSP.Problem.t -> t

val check_problem: t -> t