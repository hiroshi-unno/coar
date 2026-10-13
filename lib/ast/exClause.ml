open Core
open Common.Ext
open Common.Combinator
open LogicOld

type t = { positive : ExAtom.t Set.Poly.t; negative : ExAtom.t Set.Poly.t }

(* An example clause is a member of the version space's sets and a vertex of
   the clause graph, both of which order it by the tree shape of its two atom
   sets and of each atom's parameter map; every constructor and transformer
   in this module returns it in canonical shape (see [Common.Ext.Set.canon]),
   and anything that builds one by hand elsewhere calls this. *)
let canon cl =
  {
    positive = Set.canon (Set.Poly.map ~f:ExAtom.canon cl.positive);
    negative = Set.canon (Set.Poly.map ~f:ExAtom.canon cl.negative);
  }

let mk_false () = { positive = Set.Poly.empty; negative = Set.Poly.empty }

let mk_true () =
  {
    positive = Set.Poly.singleton (ExAtom.mk_true ());
    negative = Set.Poly.empty;
  }

let mk_unit_neg atm =
  {
    positive = Set.Poly.empty;
    negative = Set.Poly.singleton (ExAtom.canon atm);
  }

let mk_unit_pos atm =
  {
    positive = Set.Poly.singleton (ExAtom.canon atm);
    negative = Set.Poly.empty;
  }

(* assume that phi is quantifier-free *)
(* [discharge] decides a ground guard the pure part left: [`Sat] only if the
   guard is VALID (every model of the theory satisfies it), [`Unsat] if no
   model does, [`Unknown] to keep the guard.  A caller must not answer [`Sat]
   for a guard that is merely satisfiable: see the note at the use below.  The
   default keeps every guard, which is always sound. *)
let make ?(discharge = fun _ -> `Unknown) exi_senv ps ns phi =
  let of_old_atom = ExAtom.of_old_atom exi_senv (Formula.mk_true ()) in
  try
    match (*ToDo*) Evaluator.eval phi with
    | true -> None
    | false ->
        Some
          (canon
             {
               positive = Set.Poly.map ps ~f:of_old_atom;
               negative = Set.Poly.map ns ~f:of_old_atom;
             })
  with exn_ when not (Common.Timer.is_async exn_) ->
    let unknowns, params =
      Formula.term_sort_env_of phi
      |> Set.partition_tf ~f:(fst >> Map.Poly.mem exi_senv)
    in
    if Set.is_empty unknowns then (
      (* without function variables *)
      let neg_phi =
        Normalizer.normalize @@ Evaluator.simplify @@ Formula.mk_neg phi
      in
      let guarded () =
        canon
          {
            positive = Set.Poly.map ps ~f:(ExAtom.of_old_atom exi_senv neg_phi);
            negative = Set.Poly.map ns ~f:(ExAtom.of_old_atom exi_senv neg_phi);
          }
      in
      if Set.is_empty ps && Set.is_empty ns then
        (* No atom is left: the clause is its pure part [phi] alone, which the
           evaluator could not decide (it has a quantifier, a parameter or an
           open term).  There is no atom to carry the guard [neg_phi], so the
           guarded form below would be the empty clause, an UNCONDITIONAL
           refutation, whatever [phi] says.  Decide it instead: [neg_phi]
           valid means [phi] fails in every model and every instance, so the
           clause is refuted and the empty clause is right; [neg_phi]
           unsatisfiable means [phi] is valid and the clause says nothing;
           anything else is dropped, which weakens the example set and is
           always sound (a refutation would need [phi] to fail somewhere,
           which nothing here has shown). *)
        match discharge neg_phi with
        | `Sat ->
            Some (canon { positive = Set.Poly.empty; negative = Set.Poly.empty })
        | `Unsat | `Unknown -> None
      else if Set.is_empty params then
        (* The pure part is ground and still could not be evaluated, so it
           mentions a term the theory leaves open (a selector on the wrong
           constructor; division by zero is turned into a parameter earlier).
           A solution must satisfy the clause in every model, which forces the
           atoms only in the models where [neg_phi] holds.  So when the atoms
           name the same thing in every model ([ExAtom.guard_dischargeable])
           the guard is decided rather than carried: VALID, the atoms are
           unconditional; unsatisfiable, the clause says nothing; anything
           else -- satisfiable but not valid, or undecided -- keeps it.
           Dropping a guard that is merely satisfiable is unsound: two
           examples guarded by [o = 0] and [o <> 0] over an open term [o]
           would become [P(t)] and [not P(t)] and refute a satisfiable
           problem.  Otherwise the guard stays. *)
        if Set.for_all (Set.union ps ns) ~f:(ExAtom.guard_dischargeable neg_phi)
        then
          match discharge neg_phi with
          | `Sat ->
              Some
                (canon
                   {
                     positive = Set.Poly.map ps ~f:of_old_atom;
                     negative = Set.Poly.map ns ~f:of_old_atom;
                   })
          | `Unsat -> None
          | `Unknown -> Some (guarded ())
        else Some (guarded ())
      else Some (guarded ()))
    else if Set.is_empty params then
      (* with function variables and without parameters *)
      Some
        (canon
           {
             positive =
               Set.add
                 (Set.Poly.map ps ~f:of_old_atom)
                 (ExAtom.mk_fcon (Map.Poly.empty, phi));
             negative = Set.Poly.map ns ~f:of_old_atom;
           })
    else
      (* with function variables and parameters *)
      Some
        (canon
           {
             positive =
               Set.add
                 (Set.Poly.map ps ~f:of_old_atom)
                 (ExAtom.mk_fcon (Map.of_set_exn params, phi));
             negative = Set.Poly.map ns ~f:of_old_atom;
           })

(* [ExAtom.discharge_guard] on every atom; see the note there for when it is
   sound *)
let discharge_guards clause =
  canon
    {
      positive = Set.Poly.map clause.positive ~f:ExAtom.discharge_guard;
      negative = Set.Poly.map clause.negative ~f:ExAtom.discharge_guard;
    }

(* Does some atom of this clause say nothing ([ExAtom.guard_is_false])?  An
   example clause built from one clause instance gives every atom the same
   guard, so one vacuous atom means the whole instance applies nowhere; and
   where the guards differ, removing the clause is still a weakening, which is
   what a caller that drops such clauses before refuting needs. *)
let has_false_guard clause =
  Set.exists clause.positive ~f:ExAtom.guard_is_false
  || Set.exists clause.negative ~f:ExAtom.guard_is_false

let is_unit_positive (clause : t) =
  Set.is_empty clause.negative && Set.length clause.positive = 1

let is_unit_negative (clause : t) =
  Set.is_empty clause.positive && Set.length clause.negative = 1

let is_unit (clause : t) =
  Set.length clause.positive + Set.length clause.negative = 1

(* contradiction *)
let is_false (clause : t) =
  Set.(is_empty clause.positive && is_empty clause.negative)

let pvs_of (clause : t) : Ident.pvar_set =
  Set.union
    (Set.Poly.filter_map ~f:ExAtom.pvar_of clause.positive)
    (Set.Poly.filter_map ~f:ExAtom.pvar_of clause.negative)

let pvar_sorts_of (clause : t) =
  Set.union
    (Set.Poly.filter_map ~f:ExAtom.pvar_sorts_of clause.positive)
    (Set.Poly.filter_map ~f:ExAtom.pvar_sorts_of clause.negative)

let tvs_of (clause : t) : Ident.tvar_set =
  Set.concat
  @@ Set.union
       (Set.Poly.map ~f:ExAtom.tvs_of clause.positive)
       (Set.Poly.map ~f:ExAtom.tvs_of clause.negative)

let params_of clause =
  Map.of_set_exn
  @@ Set.concat_map ~f:Set.of_map
  @@ Set.union
       (Set.Poly.map ~f:ExAtom.params_of clause.positive)
       (Set.Poly.map ~f:ExAtom.params_of clause.negative)

let exatoms_of clause = Set.union clause.negative clause.positive

(* Assuming that uclause is a unit clause *)
let exatom_of_uclause (uclause : t) =
  assert (is_unit uclause);
  match (Set.choose uclause.positive, Set.choose uclause.negative) with
  | Some (ExAtom.PApp _ as atm), None
  | Some (ExAtom.FCon _ as atm), None
  | Some (ExAtom.PPApp (_, _) as atm), None
  | None, Some (ExAtom.PApp _ as atm)
  | None, Some (ExAtom.FCon _ as atm)
  | None, Some (ExAtom.PPApp (_, _) as atm) ->
      atm
  | _, _ -> assert false

let papp_of_uclause (uclause : t) =
  match exatom_of_uclause uclause with
  | ExAtom.PApp papp -> Some papp
  | _ -> None

let ppapp_of_uclause (uclause : t) =
  match exatom_of_uclause uclause with
  | ExAtom.PPApp (pred, papp) ->
      Some (pred, papp)
      (*ToDo: rename parameters to avoid introducing unnecessary dependency*)
  | _ -> None

let old_atom_of_papp ((pvar, sorts), terms) = Atom.mk_pvar_app pvar sorts terms

let old_atom_of_uclause (uclause : t) =
  uclause |> papp_of_uclause |> function
  | None -> (
      match ppapp_of_uclause uclause with
      | None -> None
      | Some ((param_senv, phi), papp) ->
          if Formula.is_true phi then Some (param_senv, old_atom_of_papp papp)
          else None (*ToDo*))
  | Some papp -> Some (Map.Poly.empty, old_atom_of_papp papp)

let atom_of_uclause uc =
  Option.(
    old_atom_of_uclause uc >>= fun (params, atm) ->
    Some (Logic.of_old_sort_env_map params, Logic.ExtTerm.of_old_atom atm))

let to_old_formula clause =
  let params_pos, positives =
    Set.unzip @@ Set.Poly.map clause.positive ~f:(ExAtom.to_old_formula true)
  in
  let params_neg, negatives =
    Set.unzip @@ Set.Poly.map clause.negative ~f:(ExAtom.to_old_formula false)
  in
  ( Map.of_set_exn
    @@ Set.concat_map ~f:Set.of_map
    @@ Set.union params_pos params_neg,
    Formula.or_of @@ Set.to_list @@ Set.union positives negatives )

let to_formula clause =
  let param_senv, phi = to_old_formula clause in
  ( Logic.of_old_sort_env_map param_senv,
    Logic.ExtTerm.of_old_formula @@ Evaluator.simplify phi )

let rename map cl =
  canon
    {
      positive = Set.Poly.map ~f:(ExAtom.rename map) cl.positive;
      negative = Set.Poly.map ~f:(ExAtom.rename map) cl.negative;
    }

let iterate_senv cl =
  let senv =
    Set.fold cl.negative ~init:([], Set.Poly.empty) ~f:ExAtom.iterate_senv
  in
  Set.fold cl.positive ~init:senv ~f:ExAtom.iterate_senv |> fst |> List.rev

let iterate_vars unknowns cl =
  let bvs, tvs =
    Set.fold cl.negative ~init:(unknowns, []) ~f:(fun (bvs, tvs) atm ->
        let bvs', tvs' = ExAtom.iterate_vars bvs atm in
        (bvs', tvs @ tvs'))
  in
  Set.fold cl.positive ~init:(bvs, tvs) ~f:(fun (bvs, tvs) atm ->
      let bvs', tvs' = ExAtom.iterate_vars bvs atm in
      (bvs', tvs @ tvs'))

let normalize_atoms cl =
  canon
    {
      positive = Set.Poly.map ~f:ExAtom.normalize cl.positive;
      negative = Set.Poly.map ~f:ExAtom.normalize cl.negative;
    }

let normalize_params unknowns cl =
  let cl = normalize_atoms cl in
  let _, tvs = iterate_vars unknowns cl in
  let map =
    Map.Poly.of_alist_exn
    @@ List.mapi tvs ~f:(fun i x ->
        (x, Ident.mk_dontcare (string_of_int (i + 1))))
  in
  rename map cl

(* [ExAtom.canon_eq_signs] on every atom; see there. *)
let canon_eq_signs cl =
  canon
    {
      positive = Set.Poly.map ~f:ExAtom.canon_eq_signs cl.positive;
      negative = Set.Poly.map ~f:ExAtom.canon_eq_signs cl.negative;
    }

let refresh_params senv cl =
  let map =
    Map.of_set_exn
    @@ Set.Poly.filter_map ~f:(fun x ->
        if Map.Poly.mem senv x then None
        else Some (x, Ident.mk_fresh_dontcare ""))
    @@ tvs_of cl
  in
  rename map cl

let str_of cl =
  let pos = String.concat_map_set ~sep:" \\/ " ~f:ExAtom.str_of cl.positive in
  let neg = String.concat_map_set ~sep:" /\\ " ~f:ExAtom.str_of cl.negative in
  String.paren @@ sprintf "%s => %s" neg pos

let normalize cl =
  canon
    {
      positive = Set.Poly.map ~f:ExAtom.normalize cl.positive;
      negative = Set.Poly.map ~f:ExAtom.normalize cl.negative;
    }

let instantiate cl =
  canon
    {
      positive = Set.Poly.map ~f:ExAtom.instantiate cl.positive;
      negative = Set.Poly.map ~f:ExAtom.instantiate cl.negative;
    }

(* the decided unit atoms paired with their first-order form, in the order
   the set iterates them.  Prepared once per propagation round: the matching
   below used to convert every unit atom again for every literal of every
   undecided clause -- 12.2 million conversions on four labeling-heavy files
   in 30 s each *)
let prepare_units atms =
  List.map (Set.to_list atms) ~f:(fun (atm, src) ->
      (atm, ExAtom.to_old_atom atm, src))

let matched_by_prepared ?(check_inst = false) unknowns units atm =
  (*ToDo: ExAtom.to_old_atom ignores conditional parametric*)
  match ExAtom.to_old_atom atm with
  | None ->
      List.find_map units ~f:(fun (atm', _, src) ->
          if ExAtom.equal atm atm' then Some (atm', src) else None (*ToDo*))
  | Some (_params (*ToDo*), atm) ->
      let inst = lazy (Atom.str_of @@ Atom.instantiate atm) in
      List.find_map units ~f:(fun (atm', old, src) ->
          match old with
          | None -> None (*ToDo*)
          | Some (_params' (*ToDo*), oatm') ->
              (* the structural match first: it fails at once on a different
                 predicate, where the printed comparison of the instantiated
                 atoms -- run first, on every pair -- was 30.6 s of the 43 s
                 the labeling phase took on 51 files *)
              if
                Option.is_some (Atom.pattern_match unknowns oatm' atm)
                && ((not check_inst)
                   || String.equal
                        (Atom.str_of @@ Atom.instantiate oatm')
                        (Lazy.force inst))
              then Some (atm', src)
              else None)

let matched_by ?(check_inst = false) unknowns atms atm =
  matched_by_prepared ~check_inst unknowns (prepare_units atms) atm

let simplify_prepared unknowns pos neg (clause, srcs) =
  let srcs = ref srcs in
  let cl_pos =
    Set.filter clause.positive ~f:(fun atm ->
        match matched_by_prepared unknowns neg atm with
        | Some (_, src) ->
            srcs := src @ !srcs;
            false
        | None -> true)
  in
  let cl_neg =
    Set.filter clause.negative ~f:(fun atm ->
        match matched_by_prepared unknowns pos atm with
        | Some (_, src) ->
            srcs := src @ !srcs;
            false
        | None -> true)
  in
  if
    Set.exists cl_pos
      ~f:(matched_by_prepared unknowns pos ~check_inst:true >> Option.is_some)
    (* clause is subsumed by pos *)
    || Set.exists cl_neg
         ~f:(matched_by_prepared unknowns neg ~check_inst:true >> Option.is_some)
    (* clause is subsumed by neg *)
    ||
    (*ToDo: this never holds?*)
    (not @@ Set.are_disjoint cl_pos cl_neg (* clause is tautology *))
  then None
  else
    Some
      (normalize_params unknowns { positive = cl_pos; negative = cl_neg }, !srcs)

let simplify unknowns pos neg =
  simplify_prepared unknowns (prepare_units pos) (prepare_units neg)

let has_self_loop ?(drop = None) terms =
  let terms = match drop with None -> terms | Some n -> List.drop terms n in
  let size = List.length terms / 2 in
  let ts1, ts2 = List.split_n terms size in
  let eq t1 t2 =
    match (t1, t2) with
    | LogicOld.(
        ( Term.FunApp (T_bv.BVNum (size1, i1), _, _),
          Term.FunApp (T_bv.BVNum (size2, i2), _, _) )) ->
        (*ToDo*)
        LogicOld.T_bv.eq_size size1 size2 && Z.equal i1 i2
    | _ -> Stdlib.( = ) t1 t2
  in
  List.equal eq ts1 ts2

let has_self_loop_exatom wfpvs = function
  | ExAtom.PApp ((pvar, _), args) ->
      (Set.mem wfpvs @@ Ident.pvar_to_tvar pvar) && has_self_loop args
  | _ -> false

let simplify_wfpvs wfpvs clause =
  if Set.exists clause.negative ~f:(has_self_loop_exatom wfpvs) then mk_true ()
  else
    canon
      {
        clause with
        positive =
          Set.filter clause.positive ~f:(has_self_loop_exatom wfpvs >> not);
      }

(* Drop from a negative clause over total predicates each atom that totality
   refutes on its own.  A clause [forall. not P(t, v) \/ R] whose existential
   variables [v] occur nowhere in [R] is [(forall v. not P(t, v)) \/ R], and
   the first disjunct is false for a total [P], so the clause says exactly [R].
   The occurrence condition is what makes this sound: without it
   [{not P(x), not Q(x)}] with both non-empty would lose both atoms and become
   the empty clause, a refutation of a satisfiable system ([P = {0}, Q = {1}]). *)
(* With [~with_positives:true] the clause may have heads and atoms of any
   unknown: an atom of [totpvs] is dropped when its existential variables
   occur in no other atom, head or body (the atom itself is unguarded, and the
   other atoms' [tvs_of] include their guards).  The argument is the same:
   [forall v. not P(t, v) \/ R] with [v] not in [R] says [R]. *)
let rec simplify_totpvs ?(with_positives = false) totpvs clause =
  if
    with_positives
    || Set.is_empty clause.positive
       && Set.for_all clause.negative ~f:(fun atm ->
           match ExAtom.pvar_of atm with
           | None -> false
           | Some p -> Map.Poly.mem totpvs @@ Ident.pvar_to_tvar p)
  then
    let droppable atm =
      match ExAtom.total_atm_vars totpvs atm with
      | None -> false
      | Some vars ->
          let rest =
            Set.union clause.positive (Set.remove clause.negative atm)
          in
          let elsewhere =
            Set.concat @@ Set.Poly.map rest ~f:ExAtom.tvs_of
          in
          Set.is_empty (Set.inter vars elsewhere)
    in
    match Set.find clause.negative ~f:droppable with
    | None -> clause
    | Some atm ->
        simplify_totpvs ~with_positives totpvs
          (canon { clause with negative = Set.remove clause.negative atm })
  else clause

let subst sub clause =
  canon
    {
      positive = Set.Poly.map clause.positive ~f:(ExAtom.subst sub);
      negative = Set.Poly.map clause.negative ~f:(ExAtom.subst sub);
    }

let add_cond phi clause =
  if Formula.is_true phi then clause
  else
    canon
      {
        positive = clause.positive;
        negative =
          Set.add clause.negative (ExAtom.mk_fcon (Map.Poly.empty, phi));
      }

(* as [add_cond], for a condition that mentions the clause's own parameters: an
   [FCon] carries its parameter environment and a term left as a parameter by a
   partial model is unbound without it *)
let add_cond_with_params params phi clause =
  if Formula.is_true phi then clause
  else
    canon
      {
        positive = clause.positive;
        negative = Set.add clause.negative (ExAtom.mk_fcon (params, phi));
      }

let exists ~f clause =
  Set.exists ~f clause.positive || Set.exists ~f clause.negative

let equal e1 e2 =
  Set.equal e1.positive e2.positive && Set.equal e1.negative e2.negative
