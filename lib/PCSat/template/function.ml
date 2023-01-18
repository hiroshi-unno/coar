open Core
open Ast
open Ast.Logic
open PCSatCommon

type parameter_update_type = ..
type parameter_update_type += TimeOut | QDep

module type Type = sig
  val params_of: tag:(Ident.tvar * Ident.tvar) option -> LogicOld.sort_env_list
  val adjust_quals: tag:(Ident.tvar * Ident.tvar) option -> LogicOld.Formula.t Set.Poly.t -> LogicOld.Formula.t Set.Poly.t
  val init_quals: (Ident.tvar * Ident.tvar) option -> LogicOld.Formula.t Set.Poly.t -> unit
  val gen_quals_terms:
    tag:(Ident.tvar * Ident.tvar) option ->
    int * LogicOld.Formula.t Set.Poly.t * (LogicOld.Formula.t , QDep.t) Map.Poly.t * LogicOld.Term.t Set.Poly.t ->
    int * LogicOld.Formula.t Set.Poly.t * (LogicOld.Formula.t , QDep.t) Map.Poly.t * LogicOld.Term.t Set.Poly.t
  val gen_template:
    tag:(Ident.tvar * Ident.tvar) option -> LogicOld.Formula.t list -> (LogicOld.Formula.t , QDep.t) Map.Poly.t -> LogicOld.Term.t list ->
    (parameter_update_type * term) * (parameter_update_type * term) list * Logic.sort_env_map * (Ident.tvar * (Ident.tvar * (LogicOld.sort_env_list * LogicOld.Formula.t)) list) list
  val next: unit -> unit
  val update_with_solution: LogicOld.Formula.t -> unit
  val update_with_labels: parameter_update_type Set.Poly.t -> unit
  val show_state: bool -> parameter_update_type Set.Poly.t -> unit
  val rl_action: parameter_update_type Set.Poly.t -> unit
  val restart: unit -> unit
  val sync: int -> unit
  val str_of: unit -> string
  val in_space: unit -> bool
end

let qdep_constr_of (qdeps : (LogicOld.Formula.t , QDep.t) Map.Poly.t) env =
  (QDep, qdeps
         |> Map.map ~f:(PCSatCommon.QDep.condition_of env) (* TODO: not empty map *)
         |> Map.Poly.to_alist
         |> List.unzip |> snd
         |> LogicOld.Formula.and_of
         |> Logic.ExtTerm.of_old_formula)
let qdep_constr_of_envs qdeps = List.map ~f:(qdep_constr_of qdeps)