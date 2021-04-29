open Core
open Ast
open Ast.Logic

type parameter_update_type = ..
type parameter_update_type += TimeOut

module type Type = sig
  val params_of: unit -> LogicOld.SortEnv.t
  val adjust_quals: LogicOld.Formula.t Set.Poly.t -> LogicOld.Formula.t Set.Poly.t
  val gen_quals_terms:
    int * LogicOld.Formula.t Set.Poly.t * LogicOld.Term.t Set.Poly.t ->
    int * LogicOld.Formula.t Set.Poly.t * LogicOld.Term.t Set.Poly.t 
  val gen_template:
    LogicOld.Formula.t list -> LogicOld.Term.t list ->
    (parameter_update_type * term) * (parameter_update_type * term) list * Logic.SortMap.t * (Ident.tvar * (Ident.tvar * (LogicOld.SortEnv.t * LogicOld.Formula.t)) list) list
  val next: unit -> unit
  val update_with_solution: LogicOld.Formula.t -> unit
  val update_with_labels: parameter_update_type Set.Poly.t -> unit
  val rl_action: parameter_update_type Set.Poly.t -> unit
  val restart: unit -> unit
  val sync: int -> unit
  val str_of: unit -> string
end