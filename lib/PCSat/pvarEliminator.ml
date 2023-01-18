open Core
open Common
open Common.Ext
open Common.Util
open Ast
open Ast.LogicOld
open PCSatCommon

module Config = struct
  type t = {
    enable : bool;
    verbose : bool;
    resolution_threshold : int;
    simplification_with_smt : bool;
    num_elim_bool_vars : int;
    propagate_lb_ub : bool;
    reduce_pvar_args : bool
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
          error_string @@ Printf.sprintf
            "Invalid PvarEliminator Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (Instance x)

  let make verbose resolution_threshold num_elim_bool_vars reduce_pvar_args =
    { enable = true;
      verbose = verbose;
      resolution_threshold = resolution_threshold;
      simplification_with_smt = true;
      num_elim_bool_vars = num_elim_bool_vars;
      propagate_lb_ub = false;
      reduce_pvar_args = reduce_pvar_args }
end

module type PvarEliminatorType = sig
  val solve : ?bpvs:(Ident.tvar Set.Poly.t) -> ?oracle:PCSP.Problem.oracle ->
    (?oracle:PCSP.Problem.oracle -> PCSP.Problem.t -> State.output Or_error.t) ->
    PCSP.Problem.t -> State.output Or_error.t
  val preprocess : ?bpvs:Ident.tvar Set.Poly.t ->
    ?oracle:CandSolOld.t option ->
    ?normalize_params:bool ->
    PCSP.Problem.t ->
    (sort_env_map * (Ident.pvar * (sort_env_list * Formula.t)) Set.Poly.t) option *
    PCSP.Problem.t
end

module Make (Config: Config.ConfigType) = struct
  let config = Config.config

  let m = Debug.Config.(if config.verbose then enable else disable)
  module Debug = Debug.Make (val m)
  module DimReducer = DimReducer.Make (val m)

  let fenv = Map.Poly.empty (*TODO: generate fenv*)
  let id:(int option ref) = ref None
  let eliminated_pvars = ref Map.Poly.empty

  let simplify_clause exi_senv (uni_senv, phi) =
    let simp =
      if config.simplification_with_smt then
        Z3Smt.Z3interface.simplify ~id:!id fenv ~timeout:(Some 20000)
      else Fn.id
    in
    let phi =
      Logic.ExtTerm.to_old_formula exi_senv uni_senv phi []
      (*|> (fun phi -> Debug.print @@ lazy ("orig: " ^ Formula.str_of phi); phi)*)
      |> Normalizer.normalize
      (*|> (fun phi -> Debug.print @@ lazy ("normalized: " ^ Formula.str_of phi); phi)*)
      |> Evaluator.simplify
      (*|> (fun phi -> Debug.print @@ lazy ("simplified: " ^ Formula.str_of phi); phi)*)
      |> (fun phi -> try simp phi with _ -> phi)
      (*|> (fun ret -> Debug.print @@ lazy ("Z3 simplified: " ^ Formula.str_of ret); ret)*)
      |> Logic.ExtTerm.of_old_formula
    in
    (*Out_channel.output_char Out_channel.stdout 'q';
      Out_channel.flush Out_channel.stdout;*)
    (* Debug.print @@ lazy ("[PvarEliminator.simplify_clause] qelim"); *)
    let uni_senv, _, phi = Qelim.qelim Map.Poly.empty exi_senv (uni_senv, [], phi) in
    (*Debug.print @@ lazy
       ("quantifier eliminated: " ^ Logic.ExtTerm.str_of_formula exi_senv uni_senv phi);*)
    uni_senv, phi
  let simplify pcsp =
    PCSP.Problem.map_if_raw pcsp
      ~f:(Set.Poly.map ~f:(simplify_clause @@ PCSP.Problem.senv_of pcsp))

  (**)let resolve_solution_of pv exi_senv clauses_pos =
        let is_resolved atm = Stdlib.(pv = Atom.pvar_of atm) in
        let tv = Ident.pvar_to_tvar pv in
        let sort = Map.Poly.find_exn exi_senv tv in
        let args =
          Logic.Sort.args_of sort |>
          List.map ~f:(fun s -> Term.mk_fresh_var @@ Logic.ExtTerm.to_old_sort s)
        in
        let eqs, param_senvs, phis =
          List.unzip3 @@
          List.map clauses_pos ~f:(fun (param_senv, ps, ns, phi) ->
              let pvatm = Set.Poly.find_exn ~f:(is_resolved) ps in
              let _, _, args0, _ = Atom.let_pvar_app pvatm in
              let eq = Formula.and_of @@ List.map2_exn args args0 ~f:(Formula.eq) in
              let ps' =
                Set.Poly.filter ps ~f:(fun atm -> Stdlib.(pv <> Atom.pvar_of atm))
                |> Set.Poly.to_list
                |> List.map ~f:Formula.mk_atom
              in
              let ns' =
                Set.Poly.to_list ns |>
                List.map ~f:(fun atm -> Formula.mk_neg @@ Formula.mk_atom atm)
              in
              let param_senv' =
                Map.Poly.to_alist param_senv
                |> List.map ~f:(fun (v, s) -> v, Logic.ExtTerm.to_old_sort s)
              in
              eq, param_senv', Formula.mk_neg @@ Formula.or_of @@ ps' @ ns' @ [phi]
            )
        in
        let params =
          List.map args ~f:Term.let_var
          |> List.map ~f:(fun ((v, s), _) -> v, Logic.ExtTerm.of_old_sort s)
        in
        Logic.ExtTerm.mk_lambda params @@
        Logic.ExtTerm.of_old_formula @@
        (fun ret ->
           Debug.print @@ lazy
             (sprintf "[resolve_solution_of] \n%s (%s) := %s"
                (Ident.name_of_pvar pv)
                (String.concat_map_list ~sep:"," args ~f:Term.str_of)
                (Formula.str_of ret));
           ret) @@
        Z3Smt.Z3interface.qelim ~id:!id (Atomic.get LogicOld.ref_fenv) @@
        Formula.exists (List.concat param_senvs) @@
        Evaluator.simplify @@
        Formula.and_of @@ eqs @ phis(**)
  let resolve qelim exi_senv pv clauses =
    Debug.print @@ lazy (sprintf "eliminating %s" @@ Ident.name_of_pvar pv);
    let is_resolved atm = Stdlib.(pv = Atom.pvar_of atm) in
    let clauses_pos, clauses_neg, clauses_rest =
      List.partition3_map clauses ~f:(fun ((_, ps, ns, _) as cl) ->
          if Set.Poly.exists ps ~f:is_resolved then `Fst cl
          else if Set.Poly.exists ns ~f:is_resolved then `Snd cl
          else `Trd cl)
    in
    (* let sol_of_pv = resolve_solution_of pv exi_senv clauses_pos in
       eliminated_pvars :=
       Map.Poly.add_exn !eliminated_pvars ~key:(Ident.pvar_to_tvar pv) ~data:sol_of_pv; *)
    let clauses_pos_lin, clauses_pos_nonlin =
      List.partition_tf clauses_pos ~f:(fun (_, ps, _, _) -> Set.Poly.count ps ~f:is_resolved = 1)
    in
    let clauses_neg_lin, clauses_neg_nonlin =
      List.partition_tf clauses_neg ~f:(fun (_, _, ns, _) -> Set.Poly.count ns ~f:is_resolved = 1)
    in
    Debug.print @@ lazy
      (sprintf "#rest %d, #poslin: %d, #posnonlin: %d, #neglin: %d, #negnonlin: %d"
         (List.length clauses_rest)
         (List.length clauses_pos_lin)
         (List.length clauses_pos_nonlin)
         (List.length clauses_neg_lin)
         (List.length clauses_neg_nonlin));
    let cls =
      clauses_rest @
      Set.Poly.to_list @@
      ClauseSetOld.simplify (Map.key_set exi_senv) (Z3Smt.Z3interface.is_valid ~id:!id fenv) @@
      Set.concat_map ~f:(fun cl ->
          let uni_senv, phi = ClauseOld.to_formula cl in
          let phi = Normalizer.normalize @@ Evaluator.simplify phi in
          let senv, phi = qelim (uni_senv, phi) in
          let phi = Normalizer.normalize @@ Evaluator.simplify phi in
          Set.Poly.map ~f:(fun (ps, ns, phi) -> senv, ps, ns, phi) @@
          Formula.cnf_of
            (Logic.to_old_sort_env_map Logic.ExtTerm.to_old_sort exi_senv)
            phi) @@
      Set.Poly.of_list @@ List.map ~f:(fun (senv, ps, ns, phis) ->
          senv, ps, ns, Formula.or_of phis) @@

      List.cartesian_map clauses_pos_lin clauses_neg_lin ~f:(fun (senv1, ps1, ns1, phi1) ncl ->
          let ps11, ps12 = Set.Poly.partition_tf ps1 ~f:is_resolved in
          Set.Poly.fold ps11 ~init:(senv1, ps12, ns1, [phi1]) ~f:(fun (senv, ps, ns, phis) -> function
              | Atom.App (_, ts1, _) -> begin
                  let senv2, ps2, ns2, phi2 = ClauseOld.refresh_tvar ncl in
                  let ns21, ns22 = Set.Poly.partition_tf ns2 ~f:is_resolved in
                  match Set.Poly.choose ns21 with
                  | Some (Atom.App (_, ts2, _)) ->
                    Map.force_merge senv senv2,
                    Set.Poly.union ps ps2,
                    Set.Poly.union ns ns22,
                    phis @ phi2 :: List.map2_exn ts1 ts2 ~f:Formula.neq
                  | _ -> assert false
                end
              | _ -> assert false)) @

      List.concat_map clauses_pos_nonlin ~f:(fun (senv1, ps1, ns1, phi1) ->
          let ps11, ps12 = Set.Poly.partition_tf ps1 ~f:is_resolved in
          Set.Poly.fold ps11 ~init:[senv1, ps12, ns1, [phi1]] ~f:(fun acc -> function
              | Atom.App (_, ts1, _) ->
                List.concat_map acc ~f:(fun (senv, ps, ns, phis) ->
                    List.map clauses_neg_lin ~f:(fun ncl ->
                        let senv2, ps2, ns2, phi2 = ClauseOld.refresh_tvar ncl in
                        let ns21, ns22 = Set.Poly.partition_tf ns2 ~f:is_resolved in
                        match Set.Poly.choose ns21 with
                        | Some (Atom.App (_, ts2, _)) ->
                          Map.force_merge senv senv2,
                          Set.Poly.union ps ps2,
                          Set.Poly.union ns ns22,
                          phis @ phi2 :: List.map2_exn ts1 ts2 ~f:Formula.neq
                        | _ -> assert false))
              | _ -> assert false)) @

      List.concat_map clauses_neg_nonlin ~f:(fun (senv1, ps1, ns1, phi1) ->
          let ns11, ns12 = Set.Poly.partition_tf ns1 ~f:is_resolved in
          Set.Poly.fold ns11 ~init:[senv1, ps1, ns12, [phi1]] ~f:(fun acc -> function
              | Atom.App (_, ts1, _) ->
                List.concat_map acc ~f:(fun (senv, ps, ns, phis) ->
                    List.map clauses_pos_lin ~f:(fun pcl ->
                        let senv2, ps2, ns2, phi2 = ClauseOld.refresh_tvar pcl in
                        let ps21, ps22 = Set.Poly.partition_tf ps2 ~f:is_resolved in
                        match Set.Poly.choose ps21 with
                        | Some (Atom.App (_, ts2, _)) ->
                          Map.force_merge senv senv2,
                          Set.Poly.union ps ps22,
                          Set.Poly.union ns ns2,
                          phis @ phi2 :: List.map2_exn ts1 ts2 ~f:Formula.neq
                        | _ -> assert false))
              | _ -> assert false))
    in
    Debug.print @@ lazy "done";
    List.iter cls ~f:(fun c -> Debug.print @@ lazy ("  " ^ ClauseOld.str_of c));
    cls

  let rec elim_one_side_unbounded_pvars exi_senv eliminable_pvs clauses =
    let pvs =
      Set.Poly.filter_map (fst @@ ClauseSetOld.count_pvar_apps eliminable_pvs clauses)
        ~f:(fun (pvar, (_dc, pc, nc)) ->
            if (*dc = 0 &&*) pc = 0 (* pvar can be false *) then begin
              Debug.print @@ lazy (sprintf "%s is assigned false because there is no LB" @@ Ident.name_of_pvar pvar);
              let params =
                mk_fresh_sort_env_list @@
                Logic.Sort.args_of @@ Map.Poly.find_exn exi_senv (Ident.pvar_to_tvar pvar)
              in
              let phi = Logic.Term.mk_lambda params @@ Logic.ExtTerm.mk_bool false in
              eliminated_pvars := Map.Poly.add_exn !eliminated_pvars ~key:(Ident.pvar_to_tvar pvar) ~data:phi;
              Some pvar
            end else if (*dc = 0 &&*) nc = 0 (* pvar can be true *) then begin
              Debug.print @@ lazy (sprintf "%s is assigned true because there is no UB" @@ Ident.name_of_pvar pvar);
              let params =
                mk_fresh_sort_env_list @@
                Logic.Sort.args_of @@ Map.Poly.find_exn exi_senv (Ident.pvar_to_tvar pvar)
              in
              let phi = Logic.Term.mk_lambda params @@ Logic.ExtTerm.mk_bool true in
              eliminated_pvars := Map.Poly.add_exn !eliminated_pvars ~key:(Ident.pvar_to_tvar pvar) ~data:phi;
              Some pvar
            end else None)
    in
    let clauses' =
      List.filter clauses ~f:(fun (_, ps, ns, _) ->
          Set.Poly.is_empty @@ Set.Poly.inter pvs (Set.Poly.map (Set.Poly.union ps ns) ~f:Atom.pvar_of))
    in
    if List.length clauses = List.length clauses' then clauses'
    else elim_one_side_unbounded_pvars exi_senv eliminable_pvs clauses'

  let subst_preds unknowns psub cls =
    let cls1, cls2 = List.partition_map cls ~f:(fun cl ->
        let cl, changed = ClauseOld.subst_preds psub cl in
        if changed then Second cl else First cl)
    in
    cls1, List.filter_map cls2 ~f:(ClauseOld.simplify unknowns (Z3Smt.Z3interface.is_valid ~id:!id fenv))

  let lbs_ubs_of exi_senv clauses =
    Pair.map (List.filter_map ~f:Fn.id) (List.filter_map ~f:Fn.id) @@
    List.unzip @@
    List.map clauses ~f:(fun (_, ps, ns, phi) ->
        Debug.print @@ lazy (sprintf "[lbs_ubs_of] %s" @@ Formula.str_of phi);
        (** assume that [phi] is alpha-renamed *)
        let lenv = Set.of_map @@ Formula.let_sort_env_of phi in
        (* let lenv = Set.Poly.empty in *)
        if Set.Poly.length ps = 1 && Set.Poly.length ns = 0 then
          match Set.Poly.choose ps with
          | Some (Atom.App (Predicate.Var (pvar, sorts), ts, _)) ->
            let xs = mk_fresh_sort_env_list sorts in
            let neqs =
              List.map2_exn ~f:Formula.neq ts (List.map xs ~f:(Combinator.uncurry Term.mk_var))
            in
            let phi' = Formula.or_of @@ phi :: neqs in
            let ys = Set.Poly.diff (Set.Poly.diff (Formula.sort_env_of phi') (Set.Poly.of_list xs)) lenv in
            let ys = Set.Poly.filter ys ~f:(fun (x, _) ->
                not @@ Set.Poly.mem (Map.key_set exi_senv) x) in
            let senv = Map.of_set_exn @@ Set.Poly.map ~f:Logic.ExtTerm.of_old_sort_bind @@ Set.Poly.union (Set.Poly.of_list xs) ys in
            Debug.print @@ lazy (sprintf "[lbs_ubs_of] senv: %s" @@ Logic.str_of_sort_env_list Logic.ExtTerm.str_of_sort @@ Map.Poly.to_alist senv);
            let _, phi'' =
              Qelim.qelim_old
                (Map.Poly.of_alist_exn @@ List.map ~f:Logic.ExtTerm.of_old_sort_bind xs)
                exi_senv (senv, phi') in
            (* (exists ys. not phi /\ xs = ts) => pvar(xs) *)
            let lb = Formula.exists (Set.Poly.to_list ys) @@ Formula.equivalent_let false @@ Normalizer.normalize_let @@ Formula.mk_neg phi'' in
            Debug.print @@ lazy (sprintf "LB of %s(%s): %s"
                                   (Ident.name_of_pvar pvar)
                                   (str_of_sort_env_list LogicOld.Term.str_of_sort xs)
                                   (Formula.str_of lb));
            Some (pvar, (xs, lb)), None
          | _ -> assert false
        else if Set.Poly.length ps = 0 && Set.Poly.length ns = 1 then
          match Set.Poly.choose ns with
          | Some (Atom.App (Predicate.Var (pvar, sorts), ts, _)) ->
            let xs = mk_fresh_sort_env_list sorts in
            let neqs =
              List.map2_exn ~f:Formula.neq ts (List.map xs ~f:(Combinator.uncurry Term.mk_var))
            in
            let phi' = Formula.or_of @@ phi :: neqs in
            let ys = Set.Poly.diff (Set.Poly.diff (Formula.sort_env_of phi') (Set.Poly.of_list xs)) lenv in
            let ys = Set.Poly.filter ys ~f:(fun (x, _) ->
                not @@ Set.Poly.mem (Map.key_set exi_senv) x) in
            let senv = Map.of_set_exn @@ Set.Poly.map ~f:Logic.ExtTerm.of_old_sort_bind @@ Set.Poly.union (Set.Poly.of_list xs) ys in
            Debug.print @@ lazy (sprintf "[lbs_ubs_of] senv: %s" @@ Logic.str_of_sort_env_list Logic.ExtTerm.str_of_sort @@ Map.Poly.to_alist senv);
            let _, phi'' =
              Qelim.qelim_old
                (Map.Poly.of_alist_exn @@ List.map ~f:Logic.ExtTerm.of_old_sort_bind xs)
                exi_senv (senv, phi')
            in
            (* pvar(xs) => (forall ys. xs = ts => phi) *)
            let ub = Formula.forall (Set.Poly.to_list ys) @@ Formula.equivalent_let true @@ Normalizer.normalize_let phi'' in
            Debug.print @@ lazy (sprintf "UB of %s(%s): %s"
                                   (Ident.name_of_pvar pvar)
                                   (str_of_sort_env_list LogicOld.Term.str_of_sort xs)
                                   (Formula.str_of ub));
            None, Some (pvar, (xs, ub))
          | _ -> assert false
        else None, None)

  let clause_of_lb pvar (senv, phi) =
    Map.Poly.of_alist_exn @@ Logic.of_old_sort_env_list Logic.ExtTerm.of_old_sort senv,
    Set.Poly.singleton @@ Atom.pvar_app_of_senv (pvar, senv),
    Set.Poly.empty,
    Formula.mk_neg phi
  let clause_of_ub pvar (senv, phi) =
    Map.Poly.of_alist_exn @@ Logic.of_old_sort_env_list Logic.ExtTerm.of_old_sort senv,
    Set.Poly.empty,
    Set.Poly.singleton @@
    Atom.pvar_app_of_senv (pvar, senv),
    phi
  let or_preds params preds =
    Formula.or_of @@ List.map preds ~f:(fun (params', phi) ->
        Formula.rename (tvar_map_of_sort_env_list params' params) phi)
  let and_preds params preds =
    Formula.and_of @@ List.map preds ~f:(fun (params', phi) ->
        Formula.rename (tvar_map_of_sort_env_list params' params) phi)
  let elim_pvars_with_lb_ub exi_senv eliminable_pvs clauses =
    let cls = ref [] in
    let psub =
      let lbs, ubs = lbs_ubs_of exi_senv clauses in
      Set.Poly.filter_map eliminable_pvs ~f:(fun pvar ->
          let pvar_lbs = List.filter_map lbs ~f:(fun (pvar', lb) -> if Stdlib.(pvar = pvar') then Some lb else None) in
          let pvar_ubs = List.filter_map ubs ~f:(fun (pvar', ub) -> if Stdlib.(pvar = pvar') then Some ub else None) in
          match pvar_lbs @ pvar_ubs with
          | [] -> None
          | (params, _) :: _ ->
            let lb = or_preds params pvar_lbs in
            let ok_lb = Set.Poly.is_empty @@ Set.Poly.inter (Formula.fvs_of lb) (Map.key_set exi_senv) in
            let ub = and_preds params pvar_ubs in
            let ok_ub = Set.Poly.is_empty @@ Set.Poly.inter (Formula.fvs_of ub) (Map.key_set exi_senv) in
            if ok_lb && Z3Smt.Z3interface.is_valid ~id:!id fenv lb then begin
              Debug.print @@ lazy (sprintf "%s is assigned true because LB is true" @@ Ident.name_of_pvar pvar);
              let phi = Logic.Term.mk_lambda (Logic.of_old_sort_env_list Logic.ExtTerm.of_old_sort params) @@ Logic.ExtTerm.mk_bool true in
              eliminated_pvars := Map.Poly.add_exn !eliminated_pvars ~key:(Ident.pvar_to_tvar pvar) ~data:phi;
              Some (pvar, (params, Formula.mk_true (), Formula.mk_false (), false))
            end else if ok_ub && Z3Smt.Z3interface.is_valid ~id:!id fenv @@ Formula.mk_neg ub then begin
              Debug.print @@ lazy (sprintf "%s is assigned false because UB is false" @@ Ident.name_of_pvar pvar);
              let phi = Logic.Term.mk_lambda (Logic.of_old_sort_env_list Logic.ExtTerm.of_old_sort params) @@ Logic.ExtTerm.mk_bool false in
              eliminated_pvars := Map.Poly.add_exn !eliminated_pvars ~key:(Ident.pvar_to_tvar pvar) ~data:phi;
              Some (pvar, (params, Formula.mk_false (), Formula.mk_true (), false))
            end else if List.exists pvar_lbs ~f:(fun (_, phi) -> Formula.is_exists phi) ||
                        List.exists pvar_ubs ~f:(fun (_, phi) -> Formula.is_forall phi) then
              None
            else if ok_lb && ok_ub && Z3Smt.Z3interface.is_valid ~id:!id fenv @@ Formula.mk_iff lb ub then begin
              Debug.print @@ lazy (sprintf "%s is assigned %s because LB and UB are equivalent" (Ident.name_of_pvar pvar) @@ Formula.str_of lb);
              let phi = Logic.Term.mk_lambda (Logic.of_old_sort_env_list Logic.ExtTerm.of_old_sort params) @@ Logic.ExtTerm.of_old_formula lb(*ToDo: ub is ignored*) in
              eliminated_pvars := Map.Poly.add_exn !eliminated_pvars ~key:(Ident.pvar_to_tvar pvar) ~data:phi;
              Some (pvar, (params, lb, Formula.mk_neg ub, false))
            end else if config.propagate_lb_ub then begin
              Debug.print @@ lazy (sprintf "LB and UB of %s are propagated" @@ Ident.name_of_pvar pvar);
              (*ToDo: this may widen the solution space?*)
              cls := (List.map ~f:(clause_of_lb pvar) pvar_lbs) @ (List.map ~f:(clause_of_ub pvar) pvar_ubs) @ !cls;
              Some (pvar, (params, lb, Formula.mk_neg ub, true))
            end else None)
      |> Map.of_set_exn
    in
    let cls1, cls2 = subst_preds (Map.key_set exi_senv) psub clauses in
    !cls @ cls1 @ cls2

  let rec elim_pvars_by_resolution qelim exi_senv eliminable_pvs clauses =
    let pvs, dc_pvs = ClauseSetOld.count_pvar_apps eliminable_pvs clauses in
    let pvs_info1, pvs_info2 =
      pvs
      |> Set.Poly.to_list
      |> List.filter_map ~f:(fun (pvar, (dc, pc, nc)) ->
          if dc = 0 && not (Set.Poly.mem dc_pvs pvar) then
            let pn = pc * nc in
            if pn <= config.resolution_threshold then Some (pvar, (pc, nc, pn)) else None
          else None)
      |> List.partition_tf ~f:(fun (pvar, (_, _, _)) ->
          let p, n =
            List.fold clauses ~init:(true, true) ~f:(fun (p, n) (senv, pos, neg, _phi) ->
                if p || n then
                  match Set.Poly.find pos ~f:(fun atm -> Set.Poly.mem (Atom.pvs_of atm) pvar) with
                  | Some atm ->
                    p &&
                    Set.Poly.is_subset
                      (ClauseOld.tvs_of (senv, Set.Poly.remove pos atm, neg, Formula.mk_true ()(*phi*)))
                      ~of_:(Atom.tvs_of atm),
                    n
                  | None ->
                    match Set.Poly.find neg ~f:(fun atm -> Set.Poly.mem (Atom.pvs_of atm) pvar) with
                    | Some atm ->
                      p,
                      n &&
                      Set.Poly.is_subset
                        (ClauseOld.tvs_of (senv, pos, Set.Poly.remove neg atm, Formula.mk_true ()(*phi*)))
                        ~of_:(Atom.tvs_of atm)
                    | None -> p, n
                else p, n)
          in p || n)
    in
    (if Fn.non List.is_empty pvs_info1 then let _ = Debug.print @@ lazy "!!" in pvs_info1
     else let _ = Debug.print @@ lazy "??" in pvs_info2)
    |> List.sort ~compare:(fun (_, (_, _, pn1)) (_, (_, _, pn2)) -> pn1 - pn2)
    |> (function
        | [] -> clauses
        | (pv, (pc, nc, _pn)) :: _rs ->
          Debug.print @@ lazy
            (sprintf "%s occurs %s times positively and %s times negatively"
               (Ident.name_of_pvar pv)
               (string_of_int pc)
               (string_of_int nc));
          let clauses' = resolve qelim exi_senv pv clauses in
          let eliminable_pvs' = Set.Poly.remove eliminable_pvs pv in
          elim_pvars_by_resolution qelim exi_senv eliminable_pvs' clauses')

  let solution_of_unit_clause clause =
    let _senv, ps, ns, phi = clause in
    let ftv = Formula.term_sort_env_of phi |> Set.Poly.elements in
    let quantifiers = fst @@ refresh_sort_env_list ftv in
    let subst_map =
      List.zip_exn ftv quantifiers
      |> List.map ~f:(fun ((tvar, sort), (bvar, sort')) ->
          assert (Stdlib.(sort = sort'));
          tvar, Term.mk_var bvar sort)
      |> Map.Poly.of_alist_exn
    in
    let phi = Formula.subst subst_map phi in
    if Set.Poly.length ps = 1 then
      match Set.Poly.choose ps with
      | Some (Atom.App (Predicate.Var (pvar, sorts), terms, _)) ->
        let phi = Evaluator.simplify @@ Formula.mk_neg phi in
        let params = sort_env_list_of_sorts sorts in
        let phi =
          try
            List.fold ~init:phi (List.zip_exn params terms)
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
        let params = sort_env_list_of_sorts sorts in
        let condition =
          try
            List.fold ~init:None (List.zip_exn params terms)
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
            Formula.forall quantifiers @@ Formula.mk_imply condition phi
          | None -> failwith "there must be at least one params"
        in
        pvar, (params, phi)
      | _ -> assert false
    else failwith "one of ps or ns has one element, the other does zero"

  let rec solve_non_rec unknowns cnf =
    let pvar, (senv, phi) =
      match List.find cnf ~f:(fun (_, ps, ns, _) -> Set.Poly.length ps + Set.Poly.length ns = 1) with
      | Some clause -> solution_of_unit_clause clause
      | None -> failwith "At least one clause must have exactly one predicate variable."
    in
    let psub = Map.Poly.singleton pvar (senv, phi, Formula.mk_neg phi, false) in
    let cnf1, cnf2 = subst_preds unknowns psub cnf in
    let cnf = cnf1 @ cnf2 in
    (pvar, (senv, phi)) ::
    if List.is_empty cnf then [] else solve_non_rec unknowns cnf

  let elim_wf_predicates pcsp = let open Logic in
    let exi_senv = PCSP.Problem.senv_of pcsp in
    let replace_wf_term term =
      let pv, args = ExtTerm.let_var_app term in
      if PCSP.Problem.is_wf_pred pcsp pv then begin
        let length = List.length args / 2 in
        assert (List.length args mod 2 = 0);
        let args_l, args_r = List.take args length, List.drop args length in
        if Stdlib.(args_l = args_r) then begin
          Debug.print @@ lazy (sprintf "eliminating %s" @@ ExtTerm.str_of term);
          ExtTerm.mk_bool false
        end else term
      end else term
    in
    PCSP.Problem.map_if_raw pcsp ~f:(fun phis ->
        Set.Poly.map phis ~f:(fun (uni_senv, phi) ->
            uni_senv,
            ExtTerm.nnf_of phi
            |> ExtTerm.cnf_of exi_senv uni_senv
            |> Set.Poly.map ~f:(fun (ps, ns, phi) ->
                uni_senv,
                Set.Poly.map ps ~f:replace_wf_term,
                Set.Poly.map ns ~f:replace_wf_term,
                phi)
            |> ClauseSet.to_formula))

  let elim_pvs ?(bpvs=Set.Poly.empty) pcsp =
    eliminated_pvars := Map.Poly.empty;
    let param_logs = DimReducer.init_param_logs_of @@ PCSP.Problem.senv_of pcsp in
    let rec inner iter pcsp0 =
      let exi_senv = PCSP.Problem.senv_of pcsp0 in
      let eliminable_pvs =
        PCSP.Problem.pvs_of pcsp0
        |> Set.Poly.filter ~f:(fun t ->
            not (Set.Poly.mem bpvs t || PCSP.Problem.is_fn_pred pcsp0 t ||
                 PCSP.Problem.is_wf_pred pcsp0 t || PCSP.Problem.is_ne_pred pcsp0 t ||
                 PCSP.Problem.is_nwf_pred pcsp0 t))
        |> Set.Poly.map ~f:(fun (Ident.Tvar n) -> Ident.Pvar n) in
      let qelim = Qelim.qelim_old Map.Poly.empty exi_senv in
      let pcsp1 =
        PCSP.Problem.remove_unused_params @@
        elim_wf_predicates @@
        PCSP.Problem.map_if_raw_old pcsp0 ~f:(fun inp ->
            (* note that phis may contain variables with the same name but different types *)
            let senvs, phis = Set.unzip @@ if iter = 0 then Set.Poly.map ~f:Formula.refresh_tvar inp else inp in
            let senv = Map.of_set_exn @@ Set.Poly.map ~f:Logic.ExtTerm.of_old_sort_bind @@ Set.concat_map ~f:Set.of_map senvs in
            Debug.print @@ lazy (sprintf "[elim_pvs] senv: %s" @@ Logic.str_of_sort_env_list Logic.ExtTerm.str_of_sort @@ Map.Poly.to_alist senv);
            Debug.print @@ lazy
              (sprintf "[elim_pvs] bpvs: %s" @@ String.concat_set ~sep:"," @@
               Set.Poly.map bpvs ~f:Ident.name_of_tvar);
            phis
            |> Set.Poly.to_list
            |> Formula.and_of
            |> Formula.cnf_of (Logic.to_old_sort_env_map Logic.ExtTerm.to_old_sort exi_senv)
            |> Set.Poly.to_list
            |> List.map ~f:(fun (ps, ns, phi) -> ClauseOld.reduce_sort_map (senv, ps, ns, phi))
            |> (fun cls ->
                Debug.print @@ lazy ("[elim_pvs] cls:");
                List.iter cls ~f:(fun c -> Debug.print @@ lazy ("  " ^ ClauseOld.str_of c));
                cls)
            (* begin: predicate variable elimination *)
            |> elim_one_side_unbounded_pvars exi_senv eliminable_pvs
            (* |> (fun cls -> Debug.print @@ lazy ("[elim_pvs]after elim_one_side_unbounded_pvars:"); List.iter cls ~f:(fun c -> Debug.print @@ lazy ("  " ^ ClauseOld.str_of c)); cls) *)
            |> elim_pvars_with_lb_ub exi_senv eliminable_pvs
            (* |> (fun cls -> Debug.print @@ lazy ("[elim_pvs]after elim_pvars_with_lb_ub:"); List.iter cls ~f:(fun c -> Debug.print @@ lazy ("  " ^ ClauseOld.str_of c)); cls) *)
            |> elim_pvars_by_resolution qelim exi_senv eliminable_pvs
            (* |> (fun cls -> Debug.print @@ lazy ("[elim_pvs]after elim_pvars_by_resolution:"); List.iter cls ~f:(fun c -> Debug.print @@ lazy ("  " ^ ClauseOld.str_of c)); cls) *)
            (* end: predicate variable elimination *)
            |> List.filter_map ~f:(fun cl ->
                let open Option in
                ClauseOld.simplify (Map.key_set exi_senv)
                  (Z3Smt.Z3interface.is_valid ~id:!id fenv) cl >>= fun cl ->
                let senv, phi = ClauseOld.to_formula @@ ClauseOld.reduce_sort_map cl in
                Some (Map.Poly.map ~f:Logic.ExtTerm.to_old_sort senv, phi))
            |> Set.Poly.of_list)
      in
      if Map.Poly.equal Stdlib.(=) (PCSP.Problem.senv_of pcsp0) (PCSP.Problem.senv_of pcsp1) then
        PCSP.Problem.remove_unused_params @@
        if config.reduce_pvar_args then
          DimReducer.elim_pcsp_args ~bpvs param_logs pcsp1
        else pcsp1
      else begin
        Debug.print @@ lazy ("*** pcsp senv has been changed, re elim_pvs");
        inner (iter + 1) pcsp1
      end
    in
    let res = inner 0 pcsp in
    !eliminated_pvars, param_logs, res
  (*ToDo: reconstruct solution for pvars eliminated by elim_pvars_by_resolution using solve_non_rec*)

  (** obsolete *)
  let const_predicates ?(bpvs=Set.Poly.empty) exi_senv (uni_senv, phis) =
    let ppvs, npvs =
      let clauses =
        Set.Poly.to_list @@
        Set.Poly.map ~f:(fun (ps, ns, phi) -> uni_senv, ps, ns, phi) @@
        Formula.cnf_of (Logic.to_old_sort_env_map Logic.ExtTerm.to_old_sort exi_senv) @@
        Formula.and_of phis
      in
      let pvar_count, _ = ClauseSetOld.count_pvar_apps bpvs clauses in
      Set.Poly.filter_map pvar_count ~f:(fun (pvar, (_, _, nc)) -> if nc = 0 then Some pvar else None),
      Set.Poly.filter_map pvar_count ~f:(fun (pvar, (_, pc, _)) -> if pc = 0 then Some pvar else None)
    in
    let pos_atoms, neg_atoms = Formula.atoms_of @@ Formula.and_of phis in
    let atoms = Set.Poly.union pos_atoms neg_atoms in
    let const_map pvs value =
      Set.Poly.map pvs ~f:(fun pv ->
          match Set.Poly.find atoms ~f:(Atom.is_pvar_app_of pv) with
          | None -> assert false
          | Some pvar_app ->
            let pvar, sorts, _, _ = Atom.let_pvar_app pvar_app in
            let params = sort_env_list_of_sorts sorts in
            (pvar, params), value)
    in
    Set.Poly.union
      (const_map ppvs (Formula.mk_true ()))
      (const_map npvs (Formula.mk_false ()))


  let expand_bool_formula exi_senv (uni_senv, phi) =
    (* assume that variables defined by uni_senv occur in phi*)
    let fvs =
      Formula.cnf_of (Logic.to_old_sort_env_map Logic.ExtTerm.to_old_sort exi_senv) phi
      |> Set.concat_map ~f:(fun (_ps, _ns, phi) ->
          (*Set.Poly.union
            (Set.concat_map ~f:Atom.fvs_of @@ Set.Poly.union ps ns) @@*)
          Formula.fvs_of phi)
    in
    let bool_senv, other_senv =
      Map.Poly.partition_mapi uni_senv ~f:(fun ~key ~data ->
          if Stdlib.(data = T_bool.SBool) && Set.Poly.mem fvs key then First data else Second data)
    in
    let num_bool_vars = Map.Poly.length bool_senv in
    if 0 < num_bool_vars && num_bool_vars <= config.num_elim_bool_vars then
      Map.Poly.to_alist bool_senv
      |> List.power (fun (x, _) -> [x, T_bool.mk_true (); x, T_bool.mk_false ()])
      |> List.map ~f:(fun map -> other_senv, Formula.subst (Map.Poly.of_alist_exn map) phi)
      |> Set.Poly.of_list
    else Set.Poly.singleton (uni_senv, phi)
  let expand_bool pcsp =
    PCSP.Problem.map_if_raw_old pcsp
      ~f:(Set.concat_map ~f:(expand_bool_formula (PCSP.Problem.senv_of pcsp)))

  let solve_and_extend solver pcsp = let open Or_error in
    solver pcsp >>= fun (sol, info) ->
    return (PCSP.Problem.extend_sol sol (PCSP.Problem.sol_for_eliminated_of pcsp), info)
  let recover_params_of_sol elimed_params_logs sol = let open Or_error in
    sol >>= fun (sol, info) ->
    let sol' =
      match sol with
      | PCSP.Problem.Sat sol ->
        PCSP.Problem.Sat (PCSP.Problem.recover_elimed_params_of_sol elimed_params_logs sol)
      | sol -> sol
    in
    return (sol', info)

  let preprocess
      ?(bpvs=Set.Poly.empty)
      ?(oracle=None)
      ?(normalize_params=false)
      pcsp =
    Debug.print @@ lazy "************* preprocessing ***************";
    Debug.print @@ lazy "input:";
    Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
    Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
    Debug.print @@ lazy "";
    Debug.print @@ lazy (FunEnv.str_of @@ PCSP.Problem.fenv_of pcsp);
    Debug.print @@ lazy "";
    let pcsp =
      PCSP.Problem.remove_unused_params @@
      simplify @@ PCSP.Problem.elim_dup_nwf_predicate @@ elim_wf_predicates @@
      simplify @@ PCSP.Problem.to_nnf @@ PCSP.Problem.normalize pcsp
    in
    Debug.print @@ lazy "normalized and simplified:";
    Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
    Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
    Debug.print @@ lazy "";
    let sol_for_eliminated, param_logs, pcsp = elim_pvs ~bpvs pcsp in
    Debug.print @@ lazy "predicate variables eliminated:";
    Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
    Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
    Debug.print @@ lazy "";
    let oracle =
      match oracle with
      | None -> None
      | Some sol ->
        Debug.print @@ lazy "oracle solution:";
        let sol' =
          PCSP.Problem.Sat
            (Map.of_set_exn @@ Set.Poly.map ~f:(fun ((x, _), t) -> x, t) @@
             snd @@ Ast.CandSol.of_old sol)
        in
        Debug.print @@ lazy (PCSP.Problem.str_of_sygus_solution sol');
        Debug.print @@ lazy "";
        let psenv, map = sol in
        Option.some @@
        (psenv,
         Set.Poly.map map ~f:(fun (pvar, (senv, phi)) ->
             let arr, _sargs = Map.Poly.find_exn param_logs pvar in
             pvar,
             (List.filteri senv ~f:(fun i _bind -> Array.get arr i), phi)))
    in
    let pcsp =
      PCSP.Problem.remove_unused_params @@
      PCSP.Problem.elim_dup_nwf_predicate @@
      simplify @@ expand_bool pcsp
    in
    Debug.print @@ lazy "boolean variables expanded:";
    Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
    Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
    Debug.print @@ lazy "";
    let pcsp = PCSP.Problem.remove_unused_params @@ simplify @@ PCSP.Problem.to_nnf pcsp in
    Debug.print @@ lazy "simplified:";
    Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
    Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
    Debug.print @@ lazy "";
    let pcsp = PCSP.Problem.to_cnf pcsp in
    Debug.print @@ lazy "output:";
    Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
    Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
    Debug.print @@ lazy "";
    let pcsp =
      if normalize_params then
        let pcsp = PCSP.Problem.normalize_uni_senv pcsp in
        Debug.print @@ lazy "universally quantified variables normalized:";
        Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
        Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        pcsp
      else pcsp
    in
    Debug.print @@ lazy (LogicOld.DTEnv.str_of @@ PCSP.Problem.dtenv_of pcsp);
    Debug.print @@ lazy "*******************************************";
    let params = PCSP.Problem.params_of pcsp in
    let params' = {
      params with
      PCSP.Params.args_record = param_logs;
      PCSP.Params.sol_for_eliminated =
        Map.force_merge sol_for_eliminated params.sol_for_eliminated
    }
    in
    let pcsp = PCSP.Problem.update_params pcsp params' in
    oracle, pcsp

  let solve
      ?(bpvs=Set.Poly.empty)
      ?(oracle=None)
      (solver : ?oracle:PCSP.Problem.oracle -> PCSP.Problem.t -> State.output Or_error.t)
      pcsp =
    id := PCSP.Problem.id_of pcsp;
    Debug.set_id !id;
    if config.enable then
      let unpreprocessable_clauses = PCSP.Problem.unpreprocessable_clauses_of pcsp in
      let bpvs = Set.Poly.union bpvs (ClauseSet.pvs_of unpreprocessable_clauses) in
      let oracle, pcsp = preprocess ~bpvs ~oracle ~normalize_params:true pcsp in
      recover_params_of_sol (PCSP.Problem.args_record_of pcsp) @@
      solve_and_extend (solver ~oracle) pcsp
    else
      let pcsp = PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf @@ PCSP.Problem.normalize pcsp in
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
      solver ~oracle pcsp
end

let make (config : Config.t) = (module Make (struct let config = config end) : PvarEliminatorType)
