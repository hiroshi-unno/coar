open Core
open Async
open Common.Util
open Ast
open Ast.LogicOld

module Config = struct
  type t = {
    verbose: bool;
    preprocess: bool;
    resolution_threshold: int;
    simplification_with_smt: bool;
    num_elim_bool_vars: int;
    propagate_lb_ub: bool;
  } [@@deriving yojson]
  module type ConfigType = sig val config : t end

  let load_ext_file = function
    | ExtFile.Filename filename ->
      begin
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename)
        >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> Ok (ExtFile.Instance x)
        | Error msg ->
          error_string
          @@ Printf.sprintf
            "Invalid PvarEliminator Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (Instance x)
end

module type PvarEliminatorType = sig
  val elim: ?bpvs:(Ident.tvar Set.Poly.t) ->
    (PCSP.Problem.t -> (PCSP.Problem.solution * int) Core.Or_error.t) ->
    PCSP.Problem.t -> (PCSP.Problem.solution * int) Core.Or_error.t
  val elim_async: ?bpvs:(Ident.tvar Set.Poly.t) ->
    (PCSP.Problem.t -> (PCSP.Problem.solution * int) Async.Deferred.Or_error.t) ->
    PCSP.Problem.t -> (PCSP.Problem.solution * int) Async.Deferred.Or_error.t
end

module Make (Config: Config.ConfigType) = struct
  let config = Config.config

  module Debug =
    Common.Debug.Make
      (val (Common.Debug.Config.(if config.verbose then enable else disable)))


  let fenv = Set.Poly.empty (*TODO: generate fenv*)

  let resolve qelim npfvs pv clauses =
    Debug.print @@ lazy ("eliminating " ^ Ident.name_of_pvar pv);
    let is_resolved atm = Stdlib.(=) pv (Atom.pvar_of atm) in
    let clauses_pos, clauses_neg, clauses_rest =
      List.partition3_map clauses ~f:(fun ((_, ps, ns, _) as cl) ->
          if Set.Poly.exists ps ~f:is_resolved then `Fst cl
          else if Set.Poly.exists ns ~f:is_resolved then `Snd cl
          else `Trd cl)
    in
    clauses_rest @
    Set.Poly.to_list @@
    ClauseSetOld.simplify npfvs (Z3Smt.Z3interface.is_valid fenv) @@
    Set.concat_map ~f:(fun cl ->
        let senv, phi = ClauseOld.to_formula cl in
        let phi = Evaluator.simplify phi in
        let senv, phi = qelim (senv, phi) in
        Set.Poly.map (Formula.cnf_of npfvs phi) ~f:(fun (ps, ns, phi) -> senv, ps, ns, phi)) @@
    Set.Poly.of_list @@
    List.cartesian_map clauses_pos clauses_neg ~f:(fun pcl ncl ->
        let (senv1, ps1, ns1, phi1) = pcl in
        let (senv2, ps2, ns2, phi2) = ncl in
        if Set.Poly.count ns2 ~f:is_resolved = 1 then
          let ps11, ps12 = Set.Poly.partition_tf ps1 ~f:is_resolved in
          Set.Poly.fold ps11 ~init:(senv1, ps12, ns1, [phi1]) ~f:(fun (senv, ps, ns, phis) -> function
              | Atom.App(_, ts1, _) -> begin
                  let (senv2, ps2, ns2, phi2) = ClauseOld.refresh_tvar ncl in
                  let ns21, ns22 = Set.Poly.partition_tf ns2 ~f:is_resolved in
                  match Set.Poly.choose ns21 with
                  | Some (Atom.App(_, ts2, _)) ->
                    Logic.SortMap.merge senv senv2,
                    Set.Poly.union ps ps2,
                    Set.Poly.union ns ns22,
                    phis @ (phi2 :: List.map2_exn ts1 ts2 ~f:Formula.neq)
                  | _ -> assert false
                end
              | _ -> assert false)
          |> (fun (senv, ps, ns, phis) -> senv, ps, ns, Formula.or_of phis)
        else (*Set.Poly.count ps1 ~f:is_resolved = 1*)
          let ns21, ns22 = Set.Poly.partition_tf ns2 ~f:is_resolved in
          Set.Poly.fold ns21 ~init:(senv2, ps2, ns22, [phi2]) ~f:(fun (senv, ps, ns, phis) -> function
              | Atom.App(_, ts2, _) -> begin
                  let (senv1, ps1, ns1, phi1) = ClauseOld.refresh_tvar pcl in
                  let ps11, ps12 = Set.Poly.partition_tf ps1 ~f:is_resolved in
                  match Set.Poly.choose ps11 with
                  | Some (Atom.App(_, ts1, _)) ->
                    Logic.SortMap.merge senv senv1,
                    Set.Poly.union ps ps12,
                    Set.Poly.union ns ns1,
                    phis @ (phi1 :: List.map2_exn ts1 ts2 ~f:Formula.neq)
                  | _ -> assert false
                end
              | _ -> assert false)
          |> (fun (senv, ps, ns, phis) -> senv, ps, ns, Formula.or_of phis))

  let elimed_pvars = ref Map.Poly.empty
  let elim_one_side_unbounded_pvars exi_senv eliminable_pvs clauses =
    let pvs =
      Set.Poly.filter_map (fst @@ ClauseSetOld.count_pvar_apps eliminable_pvs clauses)
        ~f:(fun (pvar, ( _, pc, nc)) ->
            if pc = 0 (* pvar can be false *) then begin
              Debug.print @@ lazy (Ident.name_of_pvar pvar ^ " is assigned false (because there is no positive occurrence)");
              let params =
                let sorts = Logic.Sort.args_of @@ Map.Poly.find_exn exi_senv (Ident.Tvar (Ident.name_of_pvar pvar)) in
                List.map sorts ~f:(fun sort -> Ident.mk_fresh_tvar (), sort)
              in
              let phi = Logic.Term.mk_lambda params @@ Logic.ExtTerm.mk_bool false in
              elimed_pvars := Map.Poly.add_exn !elimed_pvars ~key:(Ident.Tvar (Ident.name_of_pvar pvar)) ~data:phi;
              Some pvar
            end else if nc = 0 (* pvar can be true *) then begin
              Debug.print @@ lazy (Ident.name_of_pvar pvar ^ " is assigned true (because there is no negative occurrence)");
              let params =
                let sorts = Logic.Sort.args_of @@ Map.Poly.find_exn exi_senv (Ident.Tvar (Ident.name_of_pvar pvar)) in
                List.map sorts ~f:(fun sort -> Ident.mk_fresh_tvar (), sort)
              in
              let phi = Logic.Term.mk_lambda params @@ Logic.ExtTerm.mk_bool true in
              elimed_pvars := Map.Poly.add_exn !elimed_pvars ~key:(Ident.Tvar (Ident.name_of_pvar pvar)) ~data:phi;
              Some pvar
            end else None)
    in
    List.filter clauses ~f:(fun (_, ps, ns, _) ->
        Set.Poly.is_empty @@ Set.Poly.inter pvs (Set.Poly.map (Set.Poly.union ps ns) ~f:Atom.pvar_of))

  let subst_preds npfvs psub cls =
    let cls1, cls2 = List.partition_map cls ~f:(fun cl ->
        let cl, changed = ClauseOld.subst_preds psub cl in
        if changed then Second cl else First cl)
    in
    cls1, List.filter_map cls2 ~f:(ClauseOld.simplify npfvs (Z3Smt.Z3interface.is_valid fenv))

  let lbs_ubs_of exi_senv npfvs clauses =
    Pair.map (List.filter_map ~f:ident) (List.filter_map ~f:ident) @@
    List.unzip @@
    List.map clauses ~f:(fun (_, ps, ns, phi) ->
        if Set.Poly.length ps = 1 && Set.Poly.length ns = 0 then
          match Set.Poly.choose ps with
          | Some (Atom.App(Predicate.Var(pvar, sorts), ts, _)) ->
            let xs = List.map sorts ~f:(fun sort -> Ident.mk_fresh_tvar (), sort) in
            let neqs = List.map2_exn ~f:Formula.neq ts (List.map xs ~f:(uncurry @@ Term.mk_var)) in
            let phi' = Formula.or_of @@ phi :: neqs in
            let ys = Set.Poly.diff (Formula.term_sort_env_of phi') (Set.Poly.of_list xs) in
            let ys = Set.Poly.filter ys ~f:(fun (x, _) -> not @@ Set.Poly.mem npfvs x) in
            let senv = Map.of_set @@ Set.Poly.map ~f:Logic.ExtTerm.of_old_sort_bind @@ Set.Poly.union (Set.Poly.of_list xs) ys in
            let _, phi'' =
              Qelim.qelim_old
                (Map.Poly.of_alist_exn @@ List.map ~f:Logic.ExtTerm.of_old_sort_bind xs)
                exi_senv (senv, phi') in
            (* (exists ys. not phi /\ xs = ts) => pvar(xs) *)
            let lb = Formula.exists (SortEnv.of_set ys) (Formula.mk_neg phi'') in
            Debug.print @@ lazy ("LB of " ^ Ident.name_of_pvar pvar ^ "(" ^ (SortEnv.str_of LogicOld.Term.str_of_sort @@ SortEnv.of_list xs) ^ "): " ^ Formula.str_of lb);
            Some (pvar, (SortEnv.of_list xs, lb)), None
          | _ -> assert false
        else if Set.Poly.length ps = 0 && Set.Poly.length ns = 1 then
          match Set.Poly.choose ns with
          | Some (Atom.App(Predicate.Var(pvar, sorts), ts, _)) ->
            let xs = List.map sorts ~f:(fun sort -> Ident.mk_fresh_tvar (), sort) in
            let neqs = List.map2_exn ~f:Formula.neq ts (List.map xs ~f:(uncurry @@ Term.mk_var)) in
            let phi' = Formula.or_of @@ phi :: neqs in
            let ys = Set.Poly.diff (Formula.term_sort_env_of phi') (Set.Poly.of_list xs) in
            let ys = Set.Poly.filter ys ~f:(fun (x, _) -> not @@ Set.Poly.mem npfvs x) in
            let senv = Map.of_set @@ Set.Poly.map ~f:Logic.ExtTerm.of_old_sort_bind @@ Set.Poly.union (Set.Poly.of_list xs) ys in
            let _, phi'' =
              Qelim.qelim_old
                (Map.Poly.of_alist_exn @@ List.map ~f:Logic.ExtTerm.of_old_sort_bind xs)
                exi_senv (senv, phi') in
            (* pvar(xs) => (forall ys. xs = ts => phi) *)
            let ub = Formula.forall (SortEnv.of_set ys) phi'' in
            Debug.print @@ lazy ("UB of " ^ Ident.name_of_pvar pvar ^ "(" ^ (SortEnv.str_of LogicOld.Term.str_of_sort @@ SortEnv.of_list xs) ^ "): " ^ Formula.str_of ub);
            None, Some (pvar, (SortEnv.of_list xs, ub))
          | _ -> assert false
        else None, None)

  let clause_of_lb pvar (senv, phi) =
    (Logic.SortMap.of_old_sort_env Logic.ExtTerm.of_old_sort senv,
     Set.Poly.singleton
       (Atom.mk_pvar_app pvar
          (SortEnv.sorts_of senv)
          (List.map ~f:(uncurry Term.mk_var) @@ SortEnv.list_of senv)),
     Set.Poly.empty,
     Formula.mk_neg phi)
  let clause_of_ub pvar (senv, phi) =
    (Logic.SortMap.of_old_sort_env Logic.ExtTerm.of_old_sort senv,
     Set.Poly.empty,
     Set.Poly.singleton
       (Atom.mk_pvar_app pvar
          (SortEnv.sorts_of senv)
          (List.map ~f:(uncurry Term.mk_var) @@ SortEnv.list_of senv)),
     phi)
  let or_preds params preds =
    Formula.or_of @@ List.map preds ~f:(fun (params', phi) ->
        Formula.rename (SortEnv.from_to params' params) phi)
  let and_preds params preds =
    Formula.and_of @@ List.map preds ~f:(fun (params', phi) ->
        Formula.rename (SortEnv.from_to params' params) phi)
  let elim_pvars_with_lb_ub exi_senv npfvs eliminable_pvs clauses =
    let cls = ref [] in
    let psub =
      let lbs, ubs = lbs_ubs_of exi_senv npfvs clauses in
      Set.Poly.filter_map eliminable_pvs ~f:(fun pvar ->
          let pvar_lbs = List.filter_map lbs ~f:(fun (pvar', lb) -> if Stdlib.(=) pvar pvar' then Some lb else None) in
          let pvar_ubs = List.filter_map ubs ~f:(fun (pvar', ub) -> if Stdlib.(=) pvar pvar' then Some ub else None) in
          match pvar_lbs @ pvar_ubs with
          | [] -> None
          | (params, _) :: _ ->
            let lb = or_preds params pvar_lbs in
            let ok_lb = Set.Poly.is_empty @@ Set.Poly.inter (Formula.fvs_of lb) npfvs in
            let ub = and_preds params pvar_ubs in
            let ok_ub = Set.Poly.is_empty @@ Set.Poly.inter (Formula.fvs_of ub) npfvs in
            if ok_lb && Z3Smt.Z3interface.is_valid fenv lb then begin
              Debug.print @@ lazy (Ident.name_of_pvar pvar ^ " is assigned true because LB is true");
              let phi = Logic.Term.mk_lambda (Logic.SortEnv.of_old_sort_env Logic.ExtTerm.of_old_sort params) @@ Logic.ExtTerm.mk_bool true in
              elimed_pvars := Map.Poly.add_exn !elimed_pvars ~key:(Ident.Tvar (Ident.name_of_pvar pvar)) ~data:phi;
              Some (pvar, (params, Formula.mk_true (), Formula.mk_false (), false))
            end else if ok_ub && Z3Smt.Z3interface.is_valid fenv @@ Formula.mk_neg ub then begin
              Debug.print @@ lazy (Ident.name_of_pvar pvar ^ " is assigned false because UB is false");
              let phi = Logic.Term.mk_lambda (Logic.SortEnv.of_old_sort_env Logic.ExtTerm.of_old_sort params) @@ Logic.ExtTerm.mk_bool false in
              elimed_pvars := Map.Poly.add_exn !elimed_pvars ~key:(Ident.Tvar (Ident.name_of_pvar pvar)) ~data:phi;
              Some (pvar, (params, Formula.mk_false (), Formula.mk_true (), false))
            end else if List.exists pvar_lbs ~f:(fun (_, phi) -> Formula.is_exists phi) ||
                        List.exists pvar_ubs ~f:(fun (_, phi) -> Formula.is_forall phi) then
              None
            else if ok_lb && ok_ub && Z3Smt.Z3interface.is_valid fenv @@ Formula.mk_iff lb ub then begin
              Debug.print @@ lazy (Ident.name_of_pvar pvar ^ " is assigned because LB and UB are equivalent");
              let phi = Logic.Term.mk_lambda (Logic.SortEnv.of_old_sort_env Logic.ExtTerm.of_old_sort params) @@ Logic.ExtTerm.of_old_formula lb(*ToDo: ub is ignored*) in
              elimed_pvars := Map.Poly.add_exn !elimed_pvars ~key:(Ident.Tvar (Ident.name_of_pvar pvar)) ~data:phi;
              Some (pvar, (params, lb, Formula.mk_neg ub, false))
            end else if config.propagate_lb_ub then begin
              Debug.print @@ lazy ("LB and UB of " ^ Ident.name_of_pvar pvar ^ " are propagated");
              (*ToDo: this may widen the solution space?*)
              cls := (List.map ~f:(clause_of_lb pvar) pvar_lbs) @ (List.map ~f:(clause_of_ub pvar) pvar_ubs) @ !cls;
              Some (pvar, (params, lb, Formula.mk_neg ub, true))
            end else None)
      |> Map.of_set
    in
    let cls1, cls2 = subst_preds npfvs psub clauses in
    !cls @ cls1 @ cls2

  let rec resolve_all qelim npfvs eliminable_pvs clauses = function
    | [] -> clauses
    | (pv, (pc, nc, pn)) :: rs ->
      Debug.print @@ lazy (Ident.name_of_pvar pv ^ " occurs " ^
                           (string_of_int pc) ^ " times positively and " ^
                           (string_of_int nc) ^ " times negatively");
      let clauses' = resolve qelim npfvs pv clauses in
      let eliminable_pvs' = Set.Poly.remove eliminable_pvs pv in
      if pn <= 1 then resolve_all qelim npfvs eliminable_pvs' clauses' rs
      else elim_pvars_by_resolution qelim npfvs eliminable_pvs' clauses'
  and elim_pvars_by_resolution qelim npfvs eliminable_pvs clauses =
    let pvs, dc_pvs = ClauseSetOld.count_pvar_apps eliminable_pvs clauses in
    pvs
    |> Set.Poly.to_list
    |> List.filter_map ~f:(fun (pvar, (dc, pc, nc)) ->
        if dc = 0 && not (Set.Poly.mem dc_pvs pvar) then
          let pn = pc * nc in
          if pn <= config.resolution_threshold then Some(pvar, (pc, nc, pn)) else None
        else None)
    |> List.sort ~compare:(fun (_, (_, _, pn1)) (_, (_, _, pn2)) -> pn1 - pn2)
    |> resolve_all qelim npfvs eliminable_pvs clauses

  let solution_of_unit_clause clause =
    let (_senv, ps, ns, phi) = clause in
    let ftv = Formula.term_sort_env_of phi |> Set.Poly.elements in
    let quantifiers = SortEnv.of_list @@ List.map ~f:(fun (_, sort) -> Ident.mk_fresh_tvar (), sort) ftv in
    let subst_map =
      List.zip_exn ftv (SortEnv.list_of quantifiers)
      |> List.map ~f:(fun ((tvar, sort), (bvar, sort')) ->
          assert (Stdlib.(=) sort sort');
          tvar, Term.mk_var bvar sort)
      |> Map.Poly.of_alist_exn
    in
    let phi = Formula.subst subst_map phi in
    if Set.Poly.length ps = 1 then
      match Set.Poly.choose ps with
      | Some (Atom.App (Predicate.Var (pvar, sorts), terms, _)) ->
        let phi = Evaluator.simplify @@ Formula.mk_neg phi in
        let params = SortEnv.of_sorts sorts in
        let phi = try
            List.fold ~init:phi (List.zip_exn (SortEnv.list_of params) terms)
              ~f:(fun phi ((tvar, sort), term) ->
                  let term = Term.subst subst_map term in
                  let eq = Formula.mk_atom (T_bool.mk_eq term (Term.mk_var tvar sort)) in
                  Formula.mk_and eq phi)
          with _ -> failwith "params must be exactly same length to terms"
        in
        let phi = Formula.exists quantifiers phi in
        pvar, (params, phi)
      | _ -> assert false
    else if Set.Poly.length ns = 1 then
      match Set.Poly.choose ns with 
      | Some (Atom.App (Predicate.Var (pvar, sorts), terms, _)) ->
        let params = SortEnv.of_sorts sorts in
        let condition = try
            List.fold ~init:None (List.zip_exn (SortEnv.list_of params) terms)
              ~f:(fun condition ((tvar, sort), term) ->
                  let term = Term.subst subst_map term in
                  let eq = Formula.mk_atom (T_bool.mk_eq term (Term.mk_var tvar sort)) in
                  match condition with
                  | None -> Some eq
                  | Some phi -> Some (Formula.mk_and eq phi))
          with _ -> failwith "params must be exactly same length to terms"
        in
        let phi = 
          match condition with
          | Some condition ->
            Formula.mk_imply condition phi
            |> fun phi -> Formula.forall quantifiers phi
          | None -> failwith "there must be at least one params"
        in
        pvar, (params, phi)
      | _ -> assert false
    else failwith "one of ps or ns has one element, the other does zero"

  let rec solve_non_rec npfvs cnf =
    let pvar, (senv, phi) = 
      match List.find ~f:(fun (_, ps, ns, _) ->
          Set.Poly.length ps + Set.Poly.length ns = 1) cnf with
      | Some clause -> solution_of_unit_clause clause
      | None -> failwith "At least one clause must have exactly one predicate variable."
    in
    let psub = Map.Poly.singleton pvar (senv, phi, Formula.mk_neg phi, false) in
    let cnf1, cnf2 = subst_preds npfvs psub cnf in
    let cnf = cnf1 @ cnf2 in
    (pvar, (senv, phi)) ::
    if List.is_empty cnf then [] else solve_non_rec npfvs cnf

  let elim_pvs ?(bpvs=Set.Poly.empty) pcsp =
    let npfvs = PCSP.Problem.npfvs_of pcsp in
    let eliminable_pvs =
      Set.Poly.diff (PCSP.Problem.pvs_of pcsp)
        (Set.Poly.union_list [bpvs; PCSP.Problem.wfpvs_of pcsp; PCSP.Problem.fnpvs_of pcsp])
      |> Set.Poly.map ~f:(fun (Ident.Tvar n) -> Ident.Pvar n) in
    let qelim = Qelim.qelim_old Logic.SortMap.empty (PCSP.Problem.senv_of pcsp) in
    elimed_pvars := Map.Poly.empty;
    let pcsp =
      PCSP.Problem.map_if_raw_old pcsp
        ~f:(fun inp ->
            (* note that phis may contain variables with the same name but different types *)
            let senvs, phis = Set.unzip @@ Set.Poly.map ~f:Formula.refresh_tvar inp in
            let senv = Logic.SortMap.of_set @@ Set.Poly.map ~f:Logic.ExtTerm.of_old_sort_bind @@ Set.concat_map ~f:Set.of_map senvs in
            phis
            |> Set.Poly.to_list |> Formula.and_of |> Formula.cnf_of npfvs |> Set.Poly.to_list
            |> List.map ~f:(fun (ps, ns, phi) -> ClauseOld.reduce_sort_map @@ (senv, ps, ns, phi))
            (* begin: predicate variable elimination *)
            |> elim_one_side_unbounded_pvars (PCSP.Problem.senv_of pcsp) eliminable_pvs
            |> elim_pvars_with_lb_ub (PCSP.Problem.senv_of pcsp) npfvs eliminable_pvs
            |> elim_pvars_by_resolution qelim npfvs eliminable_pvs
            (* end: predicate variable elimination *)
            |> (List.filter_map ~f:(fun cl ->
                Option.(ClauseOld.simplify npfvs (Z3Smt.Z3interface.is_valid fenv) cl >>= fun cl ->
                        let senv, phi = ClauseOld.to_formula @@ ClauseOld.reduce_sort_map cl in
                        Some (Logic.SortMap.to_map @@ Logic.SortMap.map ~f:Logic.ExtTerm.to_old_sort senv, phi))))
            |> Set.Poly.of_list)
    in
    (*ToDo: reconstruct solution for pvars eliminated by elim_pvars_by_resolution using solve_non_rec*)
    !elimed_pvars, pcsp

  (*let get_elimed_trivial_pvars senv (phis: Formula.t list) : (Ident.pvar list * Ident.pvar list) = 
    let clauses =
      Formula.and_of phis
      |> Formula.cnf_of
      |> Set.Poly.map ~f:(fun (ps, ns, phi) -> senv, ps, ns, phi)
    in
    let pvar_count = clauses |> ClauseSetOld.count_pvar_apps |> fst in
    List.rev_filter_map pvar_count ~f:(fun (pvar, (_, _, nc)) -> if nc = 0 then Some pvar else None),
    List.rev_filter_map pvar_count ~f:(fun (pvar, (_, pc, _)) -> if pc = 0 then Some pvar else None)

    let const_predicates senv (phis: Formula.t list) =
    let ppvs, npvs = get_elimed_trivial_pvars senv phis in
    let phi = List.fold ~init:(List.hd_exn phis) (List.tl_exn phis)
        ~f:(fun phi phi' -> Formula.mk_and phi phi') in
    let pos_atoms, neg_atoms = Formula.atoms_of phi in
    let atoms = Set.Poly.union pos_atoms neg_atoms in
    let const_ value pvs =
      List.map pvs ~f:(fun pv ->
          Set.Poly.find atoms ~f:(function
              | App (Var (pv', _), _, _) -> Stdlib.(=) pv pv'
              | _ -> false))
      |> List.map ~f:(function
          | Some (Atom.App (Predicate.Var (pvar, sorts), _, _)) ->
            let params = SortEnv.of_sorts sorts in
            (pvar, params), Formula.mk_atom (value)
          | _ -> assert false) in
    const_ (Atom.mk_true ()) ppvs @ const_ (Atom.mk_false ()) npvs*)

  let simplify pcsp =
    PCSP.Problem.map_if_raw pcsp ~f:(Set.Poly.map ~f:(fun (uni_senv, phi) ->
        let phi =
          Logic.ExtTerm.of_old_formula @@
          (if config.simplification_with_smt then
             Z3Smt.Z3interface.simplify fenv ~timeout:(Some 20000)
           else ident) @@
          Evaluator.simplify @@
          (*Normalizer.normalize @@*)
          Logic.ExtTerm.to_old_formula (Logic.SortMap.merge (PCSP.Problem.senv_of pcsp) uni_senv) phi []
        in
        (*Out_channel.output_char Out_channel.stdout 'q'; Out_channel.flush Out_channel.stdout;*)
        Qelim.qelim Logic.SortMap.empty (PCSP.Problem.senv_of pcsp) (uni_senv, phi)))

  let expand_bool pcsp =
    PCSP.Problem.map_if_raw_old pcsp ~f:(Set.concat_map ~f:(fun (uni_senv, phi) ->
        (* assume that variables defined by uni_senv occur in phi*)
        let fvs =
          Formula.cnf_of (PCSP.Problem.npfvs_of pcsp) phi
          |> Set.concat_map ~f:(fun (_ps, _ns, phi) -> Formula.fvs_of phi) in
        let bool_senv, other_senv = Map.Poly.partition_mapi uni_senv ~f:(fun ~key ~data ->
            if Stdlib.(=) data T_bool.SBool && Set.Poly.mem fvs key then First data else Second data) in
        if not @@ Map.Poly.is_empty bool_senv && Map.Poly.length bool_senv <= config.num_elim_bool_vars then
          let maps =
            List.power (fun (x, _) -> [x, T_bool.mk_true (); x, T_bool.mk_false ()]) (Map.Poly.to_alist bool_senv)
          in
          Set.Poly.of_list @@
          List.map maps ~f:(fun map -> other_senv, Formula.subst (Map.Poly.of_alist_exn map) phi)
        else Set.Poly.singleton (uni_senv, phi)))

  let elim ?(bpvs=Set.Poly.empty) solver =
    if config.preprocess then
      (fun pcsp ->
         Debug.print @@ lazy "************* preprocessing ***************";
         Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
         Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
         let sol, pcsp =
           pcsp
           |> PCSP.Problem.to_nnf
           |> simplify
           |> elim_pvs ~bpvs
         in
         Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
         Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
         let pcsp =
           pcsp
           |> expand_bool
           |> simplify
           |> PCSP.Problem.remove_unused_params
         in
         Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
         Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
         let pcsp = PCSP.Problem.to_cnf pcsp in
         Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
         Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
         Debug.print @@ lazy (LogicOld.DTEnv.str_of @@ PCSP.Problem.dtenv_of pcsp);
         Debug.print @@ lazy "*******************************************";
         let open Or_error in
         solver pcsp >>= fun (sol', iters) -> return @@ (PCSP.Problem.extend_sol sol' sol, iters))
    else
      (fun pcsp ->
         let pcsp = PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf @@ pcsp in
         Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
         Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
         solver pcsp)

  (*ToDo: exactly the same code as elim*)
  let elim_async ?(bpvs=Set.Poly.empty) solver =
    if config.preprocess then
      (fun pcsp ->
         Debug.print @@ lazy "************* preprocessing ***************";
         Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
         Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
         let sol, pcsp =
           pcsp
           |> PCSP.Problem.to_nnf
           |> simplify
           |> elim_pvs ~bpvs
         in
         Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
         Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
         let pcsp =
           pcsp
           |> expand_bool
           |> simplify
           |> PCSP.Problem.remove_unused_params
         in
         Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
         Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
         let pcsp = PCSP.Problem.to_cnf pcsp in
         Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
         Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
         Debug.print @@ lazy (LogicOld.DTEnv.str_of @@ PCSP.Problem.dtenv_of pcsp);
         Debug.print @@ lazy "*******************************************";
         let open Deferred.Or_error in
         solver pcsp >>=? fun (sol', iters) -> return @@ (PCSP.Problem.extend_sol sol' sol, iters))
    else
      (fun pcsp ->
         let pcsp = PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf @@ pcsp in
         Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
         Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
         solver pcsp)
end

let make (config : Config.t) = (module Make(struct let config = config end) : PvarEliminatorType)
