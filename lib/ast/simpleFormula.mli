open Core
open LogicOld

type t =
  | ForallNode of sort_env_list * t
  | ExistsNode of sort_env_list * t
  | AndNode of t list
  | OrNode of t list
  | TopNode of unit
  | BotNode of unit
  | CondNode of pred_sym * Term.t list
  | AppNode of Ident.pvar * Term.t list

val update_bounds : sort_env_list -> sort_env_list -> sort_env_list
val mk_and : t list -> t
val mk_or : t list -> t
val mk_forall : sort_env_list -> t -> t
val mk_exists : sort_env_list -> t -> t
val mk_top : unit -> t
val mk_bot : unit -> t
val mk_cond : pred_sym -> Term.t list -> t
val mk_app : Ident.pvar -> Term.t list -> t
val mk_branch : Formula.binop -> t list -> t
val mk_bind : Formula.binder -> sort_env_list -> t -> t
val is_and : t -> bool
val is_or : t -> bool
val is_forall : t -> bool
val is_exists : t -> bool
val is_top : t -> bool
val is_bot : t -> bool
val is_cond : t -> bool
val is_app : t -> bool
val is_branch : t -> bool
val is_bind : t -> bool
val is_atom : t -> bool
val let_and : t -> t list
val let_or : t -> t list
val let_forall : t -> sort_env_list * t
val let_exists : t -> sort_env_list * t
val let_cond : t -> pred_sym * Term.t list
val let_app : t -> Ident.pvar * Term.t list
val let_branch : t -> Formula.binop * t list
val let_bind : t -> Formula.binder * sort_env_list * t

(*
  forall x, forall y -> forall x, y
  exists x, exists y -> exists x, y
  top /\ P -> P
  bot /\ P -> bot
  top \/ P -> top
  bot \/ P -> P
  (P /\ Q) /\ R -> (P /\ Q /\ R)
  (/\ [empty]) -> top
  (\/ [empty]) -> bot
*)
val simplify : t -> t
val of_formula : Formula.t -> t
val formula_of : t -> Formula.t
val get_ftv : t -> Ident.tvar Set.Poly.t
val get_fpv : t -> Ident.pvar Set.Poly.t
val mk_branch_with_simplification_one : Formula.binop -> t list -> t
val mk_bind_with_filter : Formula.binder -> sort_env_list -> t -> t
val neg : t -> t
val string_of : t -> string
