open Core
open LogicOld
open Common.Ext
open Common.Combinator

type t = Logic.sort_env_map * Atom.t Set.Poly.t * Atom.t Set.Poly.t * Formula.t

let pvs_of (_, ps, ns, _phi) = Set.union ps ns |> Set.concat_map ~f:Atom.pvs_of

let simplify_with positive negative (c_pos, c_neg, c_pure) =
  if
    Set.is_empty (Set.inter positive c_pos)
    && Set.is_empty (Set.inter negative c_neg)
  then Some (Set.diff c_pos negative, Set.diff c_neg positive, c_pure)
  else None

let rec separate vs phis =
  let phis1, phis2 =
    Set.partition_tf phis ~f:(fun (fvs, _) -> Set.is_empty @@ Set.inter fvs vs)
  in
  let dvs = Set.diff (Set.concat_map ~f:fst phis2) vs in
  if Set.is_empty dvs then (phis1, phis2)
  else
    let phis11, phis12 = separate dvs phis1 in
    (phis11, Set.union phis12 phis2)

let simplify unknowns is_valid (senv, pos, neg, phi) =
  let phi = Evaluator.simplify phi in
  let phis =
    Set.Poly.map (Formula.disjuncts_of phi) ~f:(fun phi ->
        (Formula.fvs_of phi, phi))
  in
  if Set.is_empty (Set.inter pos neg) then
    let fvs_phi = Set.concat_map ~f:fst phis in
    if Set.is_empty @@ Set.inter unknowns fvs_phi then
      let fvs_pos_neg = Set.concat_map (Set.union pos neg) ~f:Atom.fvs_of in
      let phis1, phis2 = separate fvs_pos_neg phis in
      if is_valid (Formula.or_of @@ Set.to_list (Set.Poly.map ~f:snd phis1))
      then None
      else
        Some
          ( senv,
            pos,
            neg,
            Formula.or_of @@ Set.to_list (Set.Poly.map ~f:snd phis2) )
    else Some (senv, pos, neg, phi)
  else None

let resolve_one_step mode (papp : Atom.t) (c_pos, c_neg, c_pure) =
  let open Option in
  Set.Poly.filter_map ~f:(fun papp' ->
      Atom.unify Set.Poly.empty (*ToDo: is it OK with function varibles?*) papp'
        papp
      >>= fun theta ->
      let c_pos' =
        Set.Poly.map ~f:(Atom.subst theta >> Normalizer.normalize_atom)
        @@ if Stdlib.(mode = `Backward) then Set.remove c_pos papp' else c_pos
      in
      let c_neg' =
        Set.Poly.map ~f:(Atom.subst theta >> Normalizer.normalize_atom)
        @@ if Stdlib.(mode = `Forward) then Set.remove c_neg papp' else c_neg
      in
      let c_pure' = Evaluator.simplify @@ Formula.subst theta c_pure in
      Some (c_pos', c_neg', c_pure'))
  @@ if Stdlib.(mode = `Forward) then c_neg else c_pos

(* val resolve: Atom.t Set.Poly.t -> Atom.t Set.Poly.t -> t -> t Set.Poly.t *)
let resolve_one_step_all positive negative c =
  let cs_b =
    Set.Poly.map negative ~f:(fun neg -> resolve_one_step `Backward neg c)
  in
  let cs_f =
    Set.Poly.map positive ~f:(fun pos -> resolve_one_step `Forward pos c)
  in
  Set.union cs_b cs_f |> Set.concat
  |> Set.filter ~f:(fun (_, _, pure) -> Stdlib.(pure <> Formula.mk_true ()))

let has_only_pure (pos, neg, _) = Set.is_empty pos && Set.is_empty neg

let is_query wfpvs fnpvs (pos, _, _) =
  Set.for_all pos ~f:(fun atm ->
      Atom.is_pvar_app atm
      &&
      let p = Atom.pvar_of atm in
      Set.mem wfpvs p || Set.mem fnpvs p)

let is_initializer (pos, _, _) = Set.is_empty pos

(*val refresh_tvar: (Atom.t list * Atom.t list * t) -> (Atom.t list * Atom.t list * t)*)
let refresh_tvar (senv, ps, ns, phi) =
  (*let map =
    (Formula.fvs_of phi ::
     ((ps |> Set.to_list |> List.map ~f:Atom.fvs_of) @
      (ns |> Set.to_list |> List.map ~f:Atom.fvs_of)))
    |> Set.Poly.union_list
    |> Set.Poly.map ~f:(fun x -> x, Ident.mk_fresh_tvar ())
    |> Map.of_set_exn
    in*)
  let map =
    Map.Poly.of_alist_exn @@ Map.Poly.to_alist
    @@ Map.Poly.map senv ~f:(fun _ -> Ident.mk_fresh_tvar ())
  in
  ( Map.rename_keys_map map senv,
    Set.Poly.map ~f:(Atom.rename map) ps,
    Set.Poly.map ~f:(Atom.rename map) ns,
    Formula.rename map phi )

let refresh_pvar_args ((senv, ps, ns, phi) : t) =
  let ps', pres =
    Set.unzip
    @@ Set.Poly.map ps ~f:(fun atm ->
           let pvar, sorts, args, info = Atom.let_pvar_app atm in
           let env = mk_fresh_sort_env_list sorts in
           let args' = Term.of_sort_env env in
           ( Atom.pvar_app_of_senv ~info pvar env,
             (env, List.map2_exn args args' ~f:Formula.neq) ))
  in
  let xss1, pneqss = Set.unzip pres in
  let ns', nres =
    Set.unzip
    @@ Set.Poly.map ns ~f:(fun atm ->
           let pvar, sorts, args, info = Atom.let_pvar_app atm in
           let env = mk_fresh_sort_env_list sorts in
           let args' = Term.of_sort_env env in
           ( Atom.pvar_app_of_senv ~info pvar env,
             (env, List.map2_exn args args' ~f:Formula.neq) ))
  in
  let xss2, nneqss = Set.unzip nres in
  let senv' =
    Map.force_merge senv @@ Map.of_set_exn @@ Logic.of_old_sort_env_set
    @@ Set.concat_map ~f:Set.Poly.of_list (Set.union xss1 xss2)
  in
  ( senv',
    ps',
    ns',
    Formula.or_of
    @@ (phi :: List.concat (Set.to_list pneqss))
    @ List.concat (Set.to_list nneqss) )

let tvs_of ((_senv, ps, ns, phi) : t) =
  Set.union (Formula.tvs_of phi)
  @@ Set.concat_map (Set.union ps ns) ~f:Atom.tvs_of

let fvs_of ((_senv, ps, ns, phi) : t) =
  Set.union (Formula.fvs_of phi)
  @@ Set.concat_map (Set.union ps ns) ~f:Atom.fvs_of

let reduce_sort_map ((senv, ps, ns, phi) : t) =
  let fvs = Set.inter (Map.key_set senv) (fvs_of (senv, ps, ns, phi)) in
  ( Map.of_set_exn
    @@ Set.Poly.map fvs ~f:(fun x -> (x, Map.Poly.find_exn senv x)),
    ps,
    ns,
    phi )

let to_formula (senv, ps, ns, phi) =
  ( senv,
    Formula.or_of
    @@ phi
       :: (Set.to_list
          @@ Set.union
               (Set.Poly.map ps ~f:Formula.mk_atom)
               (Set.Poly.map ns ~f:(Formula.mk_atom >> Formula.mk_neg))) )

let str_of cls = Formula.str_of @@ snd @@ to_formula cls

let subst_aux sub atoms phi is_pos : Atom.t Set.Poly.t * Formula.t * bool =
  Set.fold atoms ~init:(Set.Poly.empty, phi, false)
    ~f:(fun (atoms, phi, changed) -> function
    | Atom.App (Predicate.Var (pvar, _), _, _) as atom -> (
        match Map.Poly.find sub pvar with
        | None -> (Set.add atoms atom, phi, changed)
        | Some (params, phi_pos, phi_neg, keep) ->
            let psub =
              Map.Poly.singleton pvar
                (params, if is_pos then phi_pos else phi_neg)
            in
            ( (if keep then Set.add atoms atom else atoms),
              Formula.mk_or phi @@ Atom.subst_preds psub atom,
              true ))
    | _ -> failwith "Invalid pattern of Atom")

let subst_preds psub (senv, ps, ns, phi) =
  let ps', phi, changed1 = subst_aux psub ps phi true in
  let ns', phi, changed2 = subst_aux psub ns phi false in
  ((senv, ps', ns', phi), changed1 || changed2)
