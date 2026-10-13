open Core
open Ast
open PCSatCommon

type parameter_update_type = ..
type parameter_update_type += TimeOut | QualDep | Shape

(** [refuse_without_template f] is [f ()], except that a template generator's
    report that it has no template for the unknown -- a result sort its family
    has no form for, or a function into a universally quantified sort with no
    candidate result (no argument of that sort and none stored in a datatype
    argument) -- is raised as [PCSP.Problem.NoTemplate].  Such an unknown has
    an empty hypothesis space, so the solver cannot exhibit a solution for it
    and the answer is [unknown], an ordinary verdict; the generator's own
    exception would reach the user as a backtrace. *)
let refuse_without_template f =
  try f () with Templ.No_function_template reason ->
    raise (PCSP.Problem.NoTemplate reason)

module type Type = sig
  val name_of : unit -> Ident.tvar

  (* [kind_of] is for messages; control flow uses [kind] (the predicate kind
     the template is for) and [flexible] (a [*Flex] template, whose
     qualifiers are not refined from candidates) *)
  val kind_of : unit -> string
  val kind : Kind.t
  val flexible : bool
  val sort_of : unit -> LogicOld.Sort.t
  val params_of : unit -> LogicOld.sort_env_list

  val show_state :
    ?config:RLConfig.t -> parameter_update_type Set.Poly.t -> unit

  val str_of : unit -> string
  val in_space : unit -> bool

  val adjust_quals_terms :
    LogicOld.Formula.t Set.Poly.t * LogicOld.Term.t Set.Poly.t ->
    LogicOld.Formula.t Set.Poly.t * LogicOld.Term.t Set.Poly.t

  val update_hspace : HypSpace.hspace -> HypSpace.hspace

  val gen_template :
    ucore:
      (int list (* shape *)
      * bool (* use equality *)
      * bool (* only booleans *))
      option ->
    HypSpace.hspace ->
    (parameter_update_type * Logic.term)
    * (bool (* true: hard, false: soft *) * parameter_update_type * Logic.term)
      list
    * Logic.sort_env_map
    * (Ident.tvar
      * (Ident.tvar * (LogicOld.sort_env_list * LogicOld.Formula.t)) list)
      list

  (* the ranking-function certificate template behind the last generated
     template, for kinds that have one; [None] otherwise *)
  val kind_cert_template : unit -> Templ.kind_cert_templ option
  val actions_of : parameter_update_type Set.Poly.t -> string list
  val update_with_labels : parameter_update_type Set.Poly.t -> unit
  val rl_action : parameter_update_type Set.Poly.t -> unit
  val restart : unit -> unit
  val update_with_solution : LogicOld.Formula.t -> unit
  val sync : int -> unit
end

let qdep_constr_of_envs (qdeps : (LogicOld.Formula.t, QualDep.t) Map.Poly.t) =
  List.map ~f:(fun env ->
      ( true (*ToDo*),
        QualDep,
        Map.filter_map qdeps ~f:(fun qdep ->
            try Some (QualDep.condition_of env qdep)
            with exn_ when not (Common.Timer.is_async exn_) -> None)
        (* TODO: not empty map *)
        |> Map.Poly.data
        |> LogicOld.Formula.and_of |> Logic.ExtTerm.of_old_formula ))
