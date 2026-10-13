(* Deciding a sample's polarity from the problem's own fact and goal clauses.

   A FACT clause has no predicate in its premise and one atom in its head:
   [forall x. Phi(x) => pi(a(x))].  A GOAL clause has no head and a body whose
   predicate atoms all apply ONE predicate: [forall x. Phi(x) /\ pi(a1(x)) /\
   ... /\ pi(ak(x)) => false].  For an atom [pi(v)] the loop already holds, a
   fact clause forces [pi(v)] true, and a goal clause forces it false, wherever
   the clause has an instance that says exactly that.  This is the
   post-extraction simplification of the HoIce tool paper (Champion, Chiba,
   Kobayashi, Sato), which asks whether [Phi /\ a = v] is satisfiable; a goal
   clause with several atoms of the one predicate is taken with all of them
   identified with [pi(v)], which is an instance of the clause like any other.

   SATISFIABILITY IS NOT THE LICENCE HERE, and importing the published test
   verbatim would be unsound for this tree's semantics, in which a clause holds
   when it holds in every model of the background theory.  [Phi /\ a = v]
   being satisfiable says there is SOME model with a witness; where [Phi]
   mentions a term the theory leaves open (a selector on the wrong
   constructor, a division by zero, an out-of-range sequence read, an
   uninterpreted symbol) another model may have none, and there the clause
   does not force [pi(v)] at all.  So the two cases are:

   - GROUND atom (no parameter, no guard, closed arguments).  The solver's
     model is used only to FIND an instantiation [x := m].  What is returned is
     the clause's instance at [m], built by the same instantiation the
     validator uses for a counterexample ([ExClauseSet.of_model_with_subst]),
     and it is accepted only when that instance IS the unit [+pi(v)] (fact) or
     [-pi(v)] (goal) with no guard: every clause instance holds in every model,
     and an instance whose pure part the evaluator reduced to nothing asserts
     the unit unconditionally.  Where the pure part keeps an open term, the
     instance comes out guarded or not a unit, and it is not accepted; so the
     answer never rests on the model's choice for an open term.

   - GUARDED or PARAMETRIC atom [forall p. c => pi(t)], or a ground atom whose
     instance was not accepted.  The query is the validity of
     [c => exists x. Phi /\ a = t].  Valid means: in every model and for every
     [p] with [c], some [x] makes [Phi] true and [a(x) = t], so the clause's
     instance there gives [pi(t)] (fact) or [not pi(t)] (goal) -- which is what
     the example [forall p. c => +-pi(t)] asserts.  An atom whose query is
     satisfiable but not valid is exactly the case the published test would
     decide and this one does not.

   Anything else -- unsatisfiable, invalid, undecided within the budget, a
   formula the solver may not return on, an exception -- leaves the atom
   undecided.  Nothing is ever concluded from the absence of an answer. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

type role = Fact | Goal

type entry = {
  clause : Clause.t;
  role : role;
  pvar : Ident.pvar;
  uni_senv : Logic.sort_env_map;
  binders : sort_env_list;
  body : Formula.t;  (** [Phi], the clause's premise: the negated pure part *)
  arg_lists : Term.t list list;
      (** the arguments of each atom of [pvar]: one for a fact, one or more for
          a goal *)
}

let str_of_role = function Fact -> "fact" | Goal -> "goal"

(* [Some e] only for a fact clause (one head atom, no body atom) or a goal
   clause (no head, every body atom applying one predicate). *)
let entry_of_clause exi_senv (cl : Clause.t) : entry option =
  try
    let uni_senv, ps, ns, phi = Clause.to_old_clause exi_senv cl in
    let app = function
      | Atom.App (Predicate.Var (pv, _), args, _) -> Some (pv, args)
      | _ -> None
    in
    let binders =
      Map.Poly.to_alist @@ Map.Poly.map uni_senv ~f:Logic.ExtTerm.to_old_sort
    in
    (* a clause is [phi \/ ps \/ not ns], so its premise's pure part is the
       negation of [phi] *)
    let body = Formula.mk_neg phi in
    let mk role pvar arg_lists =
      Some { clause = cl; role; pvar; uni_senv; binders; body; arg_lists }
    in
    match (Set.to_list ps, Set.to_list ns) with
    | [ a ], [] -> (
        match app a with Some (pv, args) -> mk Fact pv [ args ] | None -> None)
    | [], (_ :: _ as atoms) -> (
        match List.map atoms ~f:app |> Option.all with
        | Some ((pv, _) :: _ as apps)
          when List.for_all apps ~f:(fun (pv', _) -> Ident.pvar_equal pv pv')
          ->
            mk Goal pv (List.map apps ~f:snd)
        | _ -> None)
    | _ -> None
  with exn_ when not (Common.Timer.is_async exn_) -> None

let entries_of_problem exi_senv clauses =
  Set.to_list clauses |> List.filter_map ~f:(entry_of_clause exi_senv)

(* Does a sort mention a sort variable (a [declare-forall-sort]), a datatype, a
   sequence or an array, anywhere in it?  An arrow sort is asked of its
   arguments and its result.  [Term.sorts_of_sort] collects the sorts a sort is
   built from but leaves an array sort itself out (only its index and element
   sorts are added), so an array is matched on the sort and on its parts
   separately. *)
let structured_sort sort =
  let args, ret = Sort.args_ret_of sort in
  List.exists (ret :: args) ~f:(fun s ->
      T_array.is_sarray s
      || Set.exists (Term.sorts_of_sort s) ~f:(fun s ->
             Sort.is_svar s || T_dt.is_sdt s || T_seq.is_sseq s
             || T_array.is_sarray s))

(* Is the problem "structured": does an unknown take a parameter, or does a
   clause bind a variable, of a sort that [structured_sort] accepts?  Decided
   from the sort environments alone (no term is converted), so it costs a walk
   over the declarations.  This is the firing condition of the resolver's
   [fact_goal_structured_only]: on a problem over integers and reals alone the
   pass's questions were measured to decide nothing the loop lacked, while
   asking them still moved the trajectory (they go to the pooled solver context
   and allocate), so there the only harmless pass is one that asks nothing. *)
let structured_problem exi_senv clauses =
  let structured_lsort so = structured_sort (Logic.ExtTerm.to_old_sort so) in
  Map.Poly.exists exi_senv ~f:structured_lsort
  || Set.exists clauses ~f:(fun cl ->
         Map.Poly.exists (Clause.sort_env_of cl) ~f:structured_lsort)

(* The resolver's gate for the pass: [enabled] is [decide_by_fact_goal_clauses],
   [structured_only] is [fact_goal_structured_only].  When it is false the pass
   returns before building an entry or asking the solver anything. *)
let fires ~enabled ~structured_only exi_senv clauses =
  enabled && ((not structured_only) || structured_problem exi_senv clauses)

(* the clause's variables are renamed apart from the atom's parameters by a
   prefix, not by a fresh name: the global fresh-name counter steers the CEGIS
   trajectory, and this must not move it *)
let prefix = "fg__"
let renamed (x, s) = (Ident.Tvar (prefix ^ Ident.name_of_tvar x), s)

let unrenamed x =
  let n = Ident.name_of_tvar x in
  if String.is_prefix n ~prefix then
    Some (Ident.Tvar (String.drop_prefix n (String.length prefix)))
  else None

let parts_of_atom = function
  | ExAtom.PApp ((pv, _), args) -> Some (pv, Map.Poly.empty, Formula.mk_true (), args)
  | ExAtom.PPApp ((params, cond), ((pv, _), args)) -> Some (pv, params, cond, args)
  | ExAtom.FCon _ -> None

(* [Phi /\ a1 = t /\ ... /\ ak = t] over the renamed clause variables, and
   those variables; [None] when the atom is not about [e.pvar], an arity
   differs, or a parameter's name could collide with a renamed variable *)
let core e atm =
  match parts_of_atom atm with
  | None -> None
  | Some (pv, params, _, args) ->
      if not (Ident.pvar_equal pv e.pvar) then None
      else if
        Map.Poly.existsi params ~f:(fun ~key ~data:_ ->
            String.is_prefix (Ident.name_of_tvar key) ~prefix)
      then None
      else
        let binders' = List.map e.binders ~f:renamed in
        let sub =
          Map.Poly.of_alist_exn
          @@ List.map2_exn e.binders binders' ~f:(fun (x, _) (y, s) ->
                 (x, Term.mk_var y s))
        in
        let eqs =
          List.map e.arg_lists ~f:(fun cargs ->
              match List.zip cargs args with
              | Unequal_lengths -> None
              | Ok pairs ->
                  Some
                    (List.map pairs ~f:(fun (ca, a) ->
                         Formula.eq (Term.subst sub ca) a)))
          |> Option.all
        in
        Option.map eqs ~f:(fun eqs ->
            ( binders',
              Formula.and_of (Formula.subst sub e.body :: List.concat eqs) ))

(* [c => exists x. Phi /\ a = t], the question whose validity decides a
   guarded or parametric atom; also what the witness checker re-asks *)
let validity_query e atm =
  match (parts_of_atom atm, core e atm) with
  | Some (_, _, cond, _), Some (binders', core) ->
      Some (Formula.mk_imply cond (Formula.exists binders' core))
  | _ -> None

let is_ground atm =
  match parts_of_atom atm with
  | Some (_, params, cond, args) ->
      Map.Poly.is_empty params && Formula.is_true cond
      && List.for_all args ~f:(fun t -> Set.is_empty (Term.tvs_of t))
  | None -> false

type answer =
  | Instance of TermSubst.t * ExClause.t
      (** the clause's instance at the substitution is this unguarded unit *)
  | Valid  (** the validity-shaped query holds *)
  | No  (** the query is unsatisfiable or invalid *)
  | Undecided

let str_of_answer = function
  | Instance _ -> "instance"
  | Valid -> "valid"
  | No -> "no"
  | Undecided -> "undecided"

(* the unit the role asserts about [atm] *)
let unit_of role atm =
  match role with
  | Fact -> ExClause.mk_unit_pos atm
  | Goal -> ExClause.mk_unit_neg atm

(* Is the instance [exs] exactly the unit [role] asserts about [atm], with no
   guard?  Compared after [ExAtom.normalize], which is how the loop stores its
   examples; a unit about a differently spelled atom is sound but decides
   nothing the loop holds, so it is not accepted. *)
let instance_is_unit role atm exs =
  match Set.to_list exs with
  | [ ex ] -> (
      let the_atom =
        match role with
        | Fact when Set.is_empty ex.ExClause.negative -> (
            match Set.to_list ex.ExClause.positive with [ a ] -> Some a | _ -> None)
        | Goal when Set.is_empty ex.ExClause.positive -> (
            match Set.to_list ex.ExClause.negative with [ a ] -> Some a | _ -> None)
        | _ -> None
      in
      match the_atom with
      | Some a ->
          let _, cond, _ = ExAtom.to_old_formula_and_cond a in
          Formula.is_true cond
          && ExAtom.equal (ExAtom.normalize a) (ExAtom.normalize atm)
      | None -> false)
  | _ -> false

(* The ground case's question: find an instantiation and build its instance.
   [discharge] is the validator's: a ground guard is dropped only when valid. *)
let decide_ground ~id ~timeout ~discharge fenv exi_senv e atm =
  match core e atm with
  | None -> `Undecided
  | Some (_binders', core) -> (
      if Z3Smt.Z3interface.may_not_return core then `Undecided
      else
        match Z3Smt.Z3interface.check_sat ~id ~timeout fenv [ core ] with
        | `Unsat -> `No
        | `Sat model -> (
            let model =
              List.filter_map model ~f:(fun ((x, s), v) ->
                  Option.map (unrenamed x) ~f:(fun x -> ((x, s), v)))
            in
            let phi_clause = Clause.to_old_formula exi_senv e.clause in
            let sub, exs =
              ExClauseSet.of_model_with_subst ~discharge exi_senv false
                (e.uni_senv, phi_clause) model
            in
            match Set.to_list exs with
            | [ ex ] when instance_is_unit e.role atm exs -> `Instance (sub, ex)
            | _ -> `Not_a_unit)
        | _ -> `Undecided)

let decide_valid ~id ~timeout fenv e atm =
  match validity_query e atm with
  | None -> Undecided
  | Some phi -> (
      if Z3Smt.Z3interface.may_not_return phi then Undecided
      else
        match Z3Smt.Z3interface.check_valid ~id ~timeout fenv phi with
        | `Valid -> Valid
        | `Invalid _ -> No
        | _ -> Undecided)

(* the decision for one atom against one clause; see the head of this file for
   why each answer is sound *)
let decide ~id ~timeout ~discharge fenv exi_senv e atm =
  try
    if is_ground atm then
      match decide_ground ~id ~timeout ~discharge fenv exi_senv e atm with
      | `Instance (sub, ex) -> Instance (sub, ex)
      | `No -> No
      | `Undecided -> Undecided
      | `Not_a_unit ->
          (* the instance kept an open term; the validity question is the
             one that can still decide the atom, in every model *)
          decide_valid ~id ~timeout fenv e atm
    else decide_valid ~id ~timeout fenv e atm
  with exn_ when not (Common.Timer.is_async exn_) -> Undecided

(* the derivation rule an example decided by [Valid] is recorded under; the
   witness checker re-asks [validity_query] of the source clause for it *)
let validity_rule = "fact-goal-validity"

(* Witness groups: deciding a head through the totality of functional
   witnesses.

   A body universal [forall q. psi(q)] skolemised into a functional (total,
   single-valued) witness [w] leaves clauses [FN_w(x, q) /\ ... => H(x)], and
   the clausal form splits [psi] over several of them sharing the atom
   [FN_w(x, q)].  A counterexample fixes [q] at the model's value, so each
   example is about one value, and since the labeling sees only
   single-valuedness it can label every [FN_w(a, v)] false and never need the
   head.  What decides the head is a case split over [q], which no example
   holds.

   A GROUP is a set of clauses with the same head atom (or none) and the same
   functional body atoms, written alike, whose results are variables [y] not
   in the head.  Member [m] has premise [Phi_m] (the negated pure part) and
   other body atoms [B_m].  The rule: if

     exists x. head(x) = v /\ forall y. \/_m (Phi_m(x, y) /\ /\_{pi(s) in B_m} U_pi(s))

   is VALID, where [U_pi(s)] is the disjunction over the decided positive
   examples [forall p. c => pi(t)] of [exists p. c /\ s = t], then [H(v)]
   holds in every solution (for a group without a head: there is no solution).

   Sound under the reading that a problem is satisfiable when every model of
   the theory admits an interpretation of the unknowns.  Fix a model and a
   solution and take [x] from the formula.  The witnesses are total, so the
   solution gives values [y0] at [x], at which every functional atom of the
   group is true.  Some member [m] then has [Phi_m(x, y0)] and every [U_pi]
   true; a decided positive example is a consequence of the problem (an
   instance of a clause, or a resolvent), so each body atom of [m] is true, and
   [m]'s instance at [(x, y0)] gives [H(v)].  Body atoms enter only positively,
   so the under-approximation [U] can only make the formula harder to prove.
   Members are closed separately; reading a shared name as one variable takes
   an instance of each.  Validity, never satisfiability, licenses the answer:
   an undecided or refused question decides nothing. *)

type wmember = {
  mclause : Clause.t;
  mbinders : sort_env_list;
  mbody : Formula.t;  (** [Phi_m] *)
  mothers : (Ident.pvar * Term.t list) list;  (** [B_m] *)
}

type wgroup = {
  ghead : (Ident.pvar * Term.t list) option;
  gys : sort_env_list;  (** the witnesses' results *)
  gmembers : wmember list;
}

let str_of_wgroup g =
  sprintf "%s <- %d clause(s) over %s"
    (match g.ghead with
    | None -> "false"
    | Some (pv, args) ->
        sprintf "%s(%s)" (Ident.name_of_pvar pv)
          (String.concat_map_list ~sep:"," args ~f:Term.str_of))
    (List.length g.gmembers)
    (String.concat_map_list ~sep:"," g.gys ~f:(fun (y, _) -> Ident.name_of_tvar y))

let wgroups_of_problem ~fnpvs exi_senv clauses =
  let app = function
    | Atom.App (Predicate.Var (pv, _), args, _) -> Some (pv, args)
    | _ -> None
  in
  let tbl = Hashtbl.Poly.create () in
  Set.iter clauses ~f:(fun cl ->
      try
        let uni_senv, ps, ns, phi = Clause.to_old_clause exi_senv cl in
        let binders =
          Map.Poly.to_alist @@ Map.Poly.map uni_senv ~f:Logic.ExtTerm.to_old_sort
        in
        match
          ( List.map (Set.to_list ps) ~f:app |> Option.all,
            List.map (Set.to_list ns) ~f:app |> Option.all )
        with
        | Some heads, Some bodies when List.length heads <= 1 -> (
            let fns, others =
              List.partition_tf bodies ~f:(fun (pv, _) ->
                  Set.mem fnpvs (Ident.pvar_to_tvar pv))
            in
            let ys =
              List.map fns ~f:(fun (_, args) ->
                  match List.last args with
                  | Some (Term.Var (y, s, _)) -> Some (y, s)
                  | _ -> None)
              |> Option.all
            in
            let head = List.hd heads in
            match ys with
            | Some (_ :: _ as ys)
              when not
                     (List.exists ys ~f:(fun (y, _) ->
                          match head with
                          | None -> false
                          | Some (_, args) ->
                              List.exists args ~f:(fun t ->
                                  Set.mem (Term.tvs_of t) y))) ->
                let key =
                  ( Option.map head ~f:(fun (pv, args) ->
                        Ident.name_of_pvar pv
                        :: List.map args ~f:Term.str_of),
                    List.sort ~compare:String.compare
                    @@ List.map fns ~f:(fun (pv, args) ->
                        Ident.name_of_pvar pv ^ "("
                        ^ String.concat_map_list ~sep:"," args ~f:Term.str_of
                        ^ ")") )
                in
                let m =
                  {
                    mclause = cl;
                    mbinders = binders;
                    mbody = Formula.mk_neg phi;
                    mothers = others;
                  }
                in
                Hashtbl.Poly.update tbl key ~f:(function
                  | None -> (head, List.dedup_and_sort ~compare:Stdlib.compare ys, [ m ])
                  | Some (h, ys', ms) -> (h, ys', m :: ms))
            | _ -> ())
        | _ -> ()
      with exn_ when not (Common.Timer.is_async exn_) -> ())
  |> fun () ->
  Hashtbl.Poly.data tbl
  |> List.map ~f:(fun (ghead, gys, ms) -> { ghead; gys; gmembers = List.rev ms })
  |> List.sort ~compare:(fun a b ->
         String.compare (str_of_wgroup a) (str_of_wgroup b))

let wprefix = "wg__"

(* [U_pi(s)] over the decided positives [pos] (atom parts: params, guard,
   arguments), each positive's parameters renamed apart by its index *)
let under pos pv args =
  Formula.or_of
  @@ List.filter_mapi pos ~f:(fun k (pv', params, cond, targs) ->
      if not (Ident.pvar_equal pv pv') then None
      else
        match List.zip args targs with
        | Unequal_lengths -> None
        | Ok pairs ->
            let ren =
              Map.Poly.to_alist params
              |> List.map ~f:(fun (x, s) ->
                  (x, (Ident.Tvar (sprintf "wgu%d__%s" k (Ident.name_of_tvar x)), s)))
            in
            let sub =
              Map.Poly.of_alist_exn
              @@ List.map ren ~f:(fun (x, (x', s)) -> (x, Term.mk_var x' s))
            in
            Some
              (Formula.exists (List.map ren ~f:snd)
                 (Formula.and_of
                    (Formula.subst sub cond
                    :: List.map pairs ~f:(fun (a, t) ->
                        Formula.eq a (Term.subst sub t))))))

(* the question rule W asks about [atm] (a head atom of the group's predicate)
   or, for a group without a head, about nothing; [None] when the atom does not
   fit the group, a member's sorts disagree, or a name could collide *)
let witness_query (g : wgroup) pos atm =
  let binders =
    List.concat_map g.gmembers ~f:(fun m -> m.mbinders)
    |> List.dedup_and_sort ~compare:Stdlib.compare
  in
  if
    List.contains_dup binders ~compare:(fun (x, _) (y, _) -> Ident.tvar_compare x y)
  then None
  else
    let ren (x, s) = (Ident.Tvar (wprefix ^ Ident.name_of_tvar x), s) in
    let sub =
      Map.Poly.of_alist_exn
      @@ List.map binders ~f:(fun ((x, _) as b) ->
          let x', s = ren b in
          (x, Term.mk_var x' s))
    in
    let is_y (x, _) = List.exists g.gys ~f:(fun (y, _) -> Ident.tvar_equal x y) in
    let xs = List.map (List.filter binders ~f:(Fn.non is_y)) ~f:ren in
    let ys = List.map g.gys ~f:ren in
    let inner =
      Formula.or_of
      @@ List.map g.gmembers ~f:(fun m ->
          Formula.and_of
            (Formula.subst sub m.mbody
            :: List.map m.mothers ~f:(fun (pv, args) ->
                under pos pv (List.map args ~f:(Term.subst sub)))))
    in
    let body = Formula.forall ys inner in
    match (g.ghead, atm) with
    | None, None -> Some (Formula.exists xs body)
    | Some (hpv, hargs), Some atm -> (
        match parts_of_atom atm with
        | Some (pv, params, cond, args)
          when Ident.pvar_equal pv hpv
               && not
                    (Map.Poly.existsi params ~f:(fun ~key ~data:_ ->
                         String.is_prefix (Ident.name_of_tvar key) ~prefix:wprefix))
          -> (
            match List.zip hargs args with
            | Unequal_lengths -> None
            | Ok pairs ->
                Some
                  (Formula.mk_imply cond
                     (Formula.exists xs
                        (Formula.and_of
                           (body
                           :: List.map pairs ~f:(fun (ha, a) ->
                               Formula.eq (Term.subst sub ha) a))))))
        | _ -> None)
    | _ -> None

let decide_witness ~id ~timeout fenv g pos atm =
  try
    match witness_query g pos atm with
    | None -> Undecided
    | Some phi -> (
        if Z3Smt.Z3interface.may_not_return phi then Undecided
        else
          match Z3Smt.Z3interface.check_valid ~id ~timeout fenv phi with
          | `Valid -> Valid
          | `Invalid _ -> No
          | _ -> Undecided)
  with exn_ when not (Common.Timer.is_async exn_) -> Undecided

let witness_rule = "witness-group-validity"
