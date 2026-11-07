open Core
open Ast
open Ast.LogicOld

type query = Formula.t
type t = { preds : Pred.t list; query : query }

type solution = Common.Verdict.t =
  | Valid
  | Invalid
  | Unknown
  | Timeout
      (** the shared verdict of [Common.Verdict]; the equation keeps
          [MuCLP.Problem.Valid] and [Verdict.Valid] interchangeable *)

val make : Pred.t list -> query -> t

exception Syntax_error of string
(** raised by the [.hes] reader for a phrase that parses but is ill-formed in
    its place: a term where a formula is expected or the converse, or a bare
    identifier in formula position that is no predicate without parameters *)
val flip_solution : solution -> solution
val str_of_solution : solution -> string
val lts_str_of_solution : solution -> string
val str_of : t -> string
val has_only_mu : t -> bool
val has_only_nu : t -> bool
val has_only_forall : t -> bool
val has_only_exists : t -> bool
val has_no_quantifier : t -> bool

val elim_neg : t -> t
(** eliminate [=>], [<=>], xor and negation by NNF and dual predicates ([P_neg]
    for [not (P _)]); identity on problems already in the
    atom/and/or/forall/exists fragment *)

val map_formula : (Formula.t -> Formula.t) -> t -> t
val size_of : t -> int

val ast_size_of : t -> int
(** the formula nodes of the query and of every predicate body; [size_of]
    counts predicates *)

val penv_of : ?init:pred_sort_env_map -> t -> pred_sort_env_map
val get_depth_ht : t -> (Ident.pvar, int) Hashtbl.Poly.t
val avoid_dup : Ident.pvar -> Ident.pvar list -> Ident.pvar
val bind_fvs_with_forall : t -> t
val refuse_free_body_vars : t -> t
(** the problem unchanged when every term variable free in a predicate's body
    is one of that predicate's parameters; otherwise raises
    [Common.Refusal.Refused] naming the variable and the predicate.  The [.hes]
    reader applies it, so no engine receives an open equation. *)
(** the problem with its query universally closed over the query's free term
    variables (never its predicate variables), each at the sort the query gives
    it; the identity on a closed query, and so idempotent.  Predicate bodies
    are unchanged.  The [.hes] reader applies it, so a problem read from a file
    reaches every engine with a closed query. *)
val aconv_tvar : t -> t
val rename_binders_apart : t -> t
(** every binder renamed to a name no other binder or variable of the problem
    spells ([x] to [x_k]); alpha-equivalent to the input, and deterministic *)

val move_quantifiers_to_front : t -> t
val rm_forall : t -> t
val simplify : t -> t
val complete_tsort : t -> t
val complete_psort : pred_sort_env_map -> t -> t
val check_problem : t -> t
