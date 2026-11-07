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

  (* the ranking-function certificate templates behind the last generated
     template, for kinds that have one; [None] otherwise.  A list of one for
     every template except the disjunctive one, whose relation is the union
     of its members' and whose certificate is their list *)
  val kind_cert_template : unit -> Templ.kind_cert_templ list option

  (* The labels a template accepts.  [parameter_update_type] is extensible and
     every template module extends it with constructors of its own, two
     modules' [Coeff] being two different constructors; a template accepts its
     own constructors and this module's [TimeOut], [QualDep] and [Shape], and
     nothing else.  [actions_of], [update_with_labels] and [rl_action] assume
     every label they are given is one of those: another module's label means
     whoever routed it confused two unknowns' templates, and they fail on it
     (an assertion) rather than guess which of their bounds it meant. *)
  val actions_of : parameter_update_type Set.Poly.t -> string list
  val update_with_labels : parameter_update_type Set.Poly.t -> unit
  val rl_action : parameter_update_type Set.Poly.t -> unit

  (* The template's own labels that grow its coefficient bounds, resp. its
     constant bounds (empty for a template without such bounds).  Every label
     listed is one [update_with_labels] accepts.  A caller that wants a
     template's bounds grown without a core having blamed them asks here
     rather than naming some template module's [Coeff]. *)
  val coeff_labels : parameter_update_type list
  val const_labels : parameter_update_type list
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

(** The solution template's starvation relaxation, for a positive [force_after]
    ([n] below): after [n] consecutive unsat cores that blamed no coefficient
    bound, every unknown the latest core names is also given those of its
    coefficient labels that the query offered no constraint for; after [500 n]
    consecutive cores that blamed no constant bound, likewise its constant
    labels.

    The relaxation exists for a bound that no core *can* name: a template that
    asks for no affine atom states no coefficient-bound constraint, so the
    search never learns that the bound is in the way.  Where the query did
    state the bound (as a labelled soft constraint a core may include) and the
    core left it out, the core has already said that bound is not to blame,
    and raising it anyway only enlarges the next query's search space (the
    bound is not to blame for the latest query, since that query is unsat
    without it): on a
    functional unknown, raising every coefficient bound on almost every round
    took the coefficient range from 1 to over 100 and kept the search from the
    small-coefficient solution the plain blame reaches.  So a label is added
    only where [offered p l] is false.

    [template_of p] is unknown [p]'s template, [None] for a name no template
    owns.  [offered p l] holds when the template in use -- the one the
    candidate search asks about, not a probe asked while learning
    qualifiers -- states a constraint labelled [l] for [p], one a core of
    that search could have named.  [pvar_labels_map] maps
    each unknown the core names to its labels.  Assumes: every label of [p] is
    one [template_of p] accepts, as a core's labels are (each template hands
    out only its own).  Guarantees the same of the result -- [p] gains only
    labels its own template lists in [coeff_labels] / [const_labels], and
    among them only those not [offered]; so no template is ever handed another
    module's label, and a bound the core could have blamed is never raised
    against the core's word.  A name without a template gains nothing, which
    loses nothing, since labels reach a template only through
    [update_with_labels] of the template owning the name.  Preserves the map's
    keys.  A core "blamed a coefficient bound" when some unknown's labels
    include one its own template lists in [coeff_labels] (likewise constants);
    [starved_coeff] and [starved_const] count the consecutive cores that did
    not, are updated in place, and are reset when the relaxation they govern
    fires, whether or not it added a label. *)
let relax_starved ~(template_of : Ident.tvar -> (module Type) option)
    ~(offered : Ident.tvar -> parameter_update_type -> bool) ~force_after
    ~starved_coeff ~starved_const pvar_labels_map =
  let coeff (module FT : Type) = FT.coeff_labels in
  let const (module FT : Type) = FT.const_labels in
  let owned select pvar =
    Option.value_map (template_of pvar) ~default:[] ~f:select
  in
  let blamed select =
    Map.Poly.existsi pvar_labels_map ~f:(fun ~key ~data ->
        let own = owned select key in
        Set.exists data ~f:(List.mem own ~equal:Stdlib.( = )))
  in
  let count counter select =
    if blamed select then counter := 0 else incr counter
  in
  count starved_coeff coeff;
  count starved_const const;
  let relax counter every select map =
    if !counter < every then map
    else (
      counter := 0;
      Map.Poly.mapi map ~f:(fun ~key ~data ->
          Set.union data
            (Set.Poly.of_list
               (List.filter (owned select key) ~f:(fun l ->
                    not (offered key l))))))
  in
  relax starved_const (500 * force_after) const
  @@ relax starved_coeff force_after coeff pvar_labels_map
