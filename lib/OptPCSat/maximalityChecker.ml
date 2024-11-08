open Core
open Common
open Common.Ext
open Common.Util
open Ast
open Ast.Ident
open Ast.Logic

module Make (Config : Config.ConfigType) :
  OptimalityChecker.OptimalityCheckerType = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_module_name "MaximalityChecker"
  let _ = OptimalityChecker.Debug.set_enable config.verbose
  let term_in_other_sol = false

  let pcsp_solver_of =
    let solvers = Hashtbl.Poly.create () in
    fun p ->
      Hashtbl.Poly.find_or_add solvers p ~default:(fun _ ->
          match ExtFile.unwrap config.opt_check_solver with
          | Ok cfg -> PCSPSolver.Solver.make cfg
          | Error exn -> Error.raise exn)

  let init_bwd_theta_of w p exi_senv theta =
    Map.Poly.filter_mapi exi_senv ~f:(fun ~key:p_y ~data:sort ->
        if not @@ Map.Poly.mem theta p_y then None
        else
          let sargs = Sort.args_of sort in
          let args =
            List.map sargs ~f:(fun _ -> ExtTerm.mk_var (mk_fresh_tvar ()))
          in
          let param_senv =
            List.map2_exn args sargs ~f:(fun v s ->
                (fst @@ ExtTerm.let_var v, s))
          in
          let pure_phi =
            ExtTerm.beta_reduction
              (Term.mk_apps (Map.Poly.find_exn theta p_y) args)
            |> fun phi ->
            if Stdlib.(p = p_y) then
              ExtTerm.or_of [ OptimalityChecker.eqs_of sargs w args; phi ]
            else ExtTerm.mk_bool false
          in
          Option.some @@ ExtTerm.mk_lambda param_senv pure_phi)

  let backward_of p p_has_trans_clause pysenv bwd_theta idx_map (nwf : Kind.nwf)
      theta w ((idw, _), w_sorts, dom_w) exi_senv i (uni_senv, ps, ns, phi) =
    assert (Set.is_singleton ps);
    Debug.print @@ lazy "";
    Debug.print @@ lazy "";
    Debug.print_log ~tag:"*** backward_of"
    @@ lazy (Clause.str_of exi_senv (uni_senv, ps, ns, phi));
    let p_y, args_y =
      Set.to_list ps |> List.hd_exn |> Term.let_apps |> fun (p_y, args_y) ->
      (fst @@ Term.let_var p_y, args_y)
    in
    let p_y_subst =
      List.zip_exn
        (List.map ~f:(fun t -> fst @@ Term.let_var t) args_y)
        (Map.Poly.find_exn pysenv p_y |> List.map ~f:fst)
      |> Map.Poly.of_alist_exn
    in
    let p_xs, args_xs =
      Set.to_list ns |> List.map ~f:Term.let_apps
      |> List.map ~f:(fun (p, args) -> (fst @@ Term.let_var p, args))
      |> List.unzip
    in
    let (_, _), sorts_0, pdom_0 = Map.Poly.find_exn idx_map p_y in
    let idxs, sortss, pdoms =
      List.unzip3 @@ List.map p_xs ~f:(Map.Poly.find_exn idx_map)
    in
    let pf = OptimalityChecker.pn (Tvar "FNb") i in
    let pfs_senv, pfapps =
      List.zip3_exn idxs args_xs sortss
      |> List.concat_mapi ~f:(fun j ((idx, p_x), arg_xs, sorts) ->
             List.mapi (List.zip_exn arg_xs sorts) ~f:(fun k (x, s) ->
                 let pfi =
                   OptimalityChecker.pnc
                     (OptimalityChecker.pnt (OptimalityChecker.pn pf j) p_x)
                     k
                 in
                 let pfi_sort =
                   Sort.mk_fun @@ w_sorts @ sorts_0 @ [ s; ExtTerm.SBool ]
                 in
                 let fn_args = w @ args_y in
                 let fn_ret = x in
                 let pfapp = ExtTerm.mk_var_app pfi @@ fn_args @ [ fn_ret ] in
                 let pfapp =
                   if idx = idw && not p_has_trans_clause then
                     let theta_p =
                       OptimalityChecker.apply_pred theta p arg_xs
                     in
                     ( Some (OptimalityChecker.eqs_of w_sorts w arg_xs),
                       ExtTerm.and_of [ theta_p; pfapp ] )
                   else (None, pfapp)
                 in
                 ((pfi, pfi_sort), ((pfi, (idx, j)), (pfapp, (fn_args, fn_ret))))))
      |> List.unzip
    in
    let wfs_senv, wfapps =
      List.unzip
      @@ List.map2_exn p_xs args_xs ~f:(fun p_x args_x ->
             let wf, wfsort, appterm =
               Kind.app_nwf_predicate nwf w (p_y, args_y) (p_x, args_x)
             in
             ( (wf, wfsort),
               if Stdlib.(p_x = p) && not p_has_trans_clause then
                 ExtTerm.mk_bool true
               else appterm ))
    in
    let exi_senv =
      Map.force_merge_list
        (* ~catch_dup:(fun (key, data1, data2) ->
            L.debug @@ sprintf "%s : %s != %s" (name_of_tvar key) (ExtTerm.str_of_sort data1) (ExtTerm.str_of_sort data2)) *)
        [
          exi_senv;
          Map.Poly.of_alist_exn
          @@ List.dedup_and_sort ~compare:Stdlib.compare pfs_senv;
          Map.Poly.of_alist_exn
          @@ List.dedup_and_sort ~compare:Stdlib.compare wfs_senv;
        ]
    in
    let bound =
      Map.Poly.of_alist_exn
      @@ List.map
           (args_y @ List.concat args_xs)
           ~f:(fun t ->
             let v, _ = ExtTerm.let_var t in
             (v, Map.Poly.find_exn uni_senv v))
    in
    let fvs, pure_phi =
      OptimalityChecker.apply_qelim_on_pure_formula bound exi_senv uni_senv
      @@ ExtTerm.neg_of phi
    in
    Debug.print_log ~tag:"pure_formula"
    @@ lazy (ExtTerm.str_of_formula exi_senv uni_senv pure_phi);
    assert (List.is_empty fvs);
    let sol_apply_map =
      List.mapi (List.zip_exn p_xs args_xs) ~f:(fun j (p_x, args) ->
          let psi =
            ExtTerm.and_of
              [
                ExtTerm.mk_var_app (List.nth_exn pdoms j) @@ w @ args;
                List.nth_exn wfapps j;
              ]
          in
          let phi =
            if Stdlib.(p_x = p) then
              ExtTerm.or_of
                [
                  OptimalityChecker.apply_pred theta p_x args;
                  OptimalityChecker.eqs_of w_sorts w args;
                ]
            else if term_in_other_sol then
              OptimalityChecker.apply_pred theta p_x args
            else ExtTerm.mk_bool false
          in
          (j, (phi, psi)))
      |> Set.Poly.of_list |> Set.to_list |> Map.Poly.of_alist_exn
    in
    let pure_phi, sol_apply_map, pfapps, eqsubst =
      OptimalityChecker.filter_pfapps exi_senv uni_senv pfapps pure_phi
        sol_apply_map
    in
    let psubst =
      if p_has_trans_clause then Map.Poly.empty
      else
        Map.Poly.singleton dom_w
          (ExtTerm.mk_lambda (mk_fresh_sort_env_list (w_sorts @ w_sorts))
          @@ ExtTerm.mk_bool true)
    in
    let head =
      ExtTerm.subst psubst @@ ExtTerm.subst eqsubst @@ ExtTerm.and_of
      @@ List.cons pure_phi
      @@ List.mapi (List.zip_exn p_xs args_xs) ~f:(fun j (_, _) ->
             let app_phi, dom_phi = Map.Poly.find_exn sol_apply_map j in
             match
               OptimalityChecker.check exi_senv uni_senv pure_phi app_phi
             with
             | Some true -> ExtTerm.mk_bool true
             | Some false -> dom_phi
             | None -> ExtTerm.or_of [ app_phi; dom_phi ])
    in
    Debug.print_log ~tag:"head"
    @@ lazy (ExtTerm.str_of_formula exi_senv uni_senv head);
    let head_fvs = ExtTerm.fvs_of head in
    let special_pfapps, pfapps =
      List.fold pfapps ~init:(Map.Poly.empty, [])
        ~f:(fun (acc, pfapps) ((_, (idx, j)), ((phi_pf, pfapp), (_, sol))) ->
          let v, _ = ExtTerm.let_var sol in
          if idx <> idw || p_has_trans_clause || Option.is_none phi_pf then
            (acc, if Set.mem head_fvs v then pfapp :: pfapps else pfapps)
          else
            let pfapp =
              if Set.mem head_fvs v then pfapp else ExtTerm.mk_bool true
            in
            ( Map.Poly.update acc j ~f:(function
                | None -> [ (Option.value_exn phi_pf, pfapp) ]
                | Some ts -> [ (Option.value_exn phi_pf, pfapp) ] @ ts),
              pfapps ))
    in
    let special_pfappss =
      Map.Poly.to_alist special_pfapps
      |> List.unzip |> snd
      |> List.map ~f:(fun special_pfapps ->
             let phis, pfapps = List.unzip special_pfapps in
             let phis = List.dedup_and_sort ~compare:Stdlib.compare phis in
             [
               ExtTerm.or_of @@ phis;
               ExtTerm.subst eqsubst @@ ExtTerm.and_of pfapps;
             ])
      |> List.permutation_without_repetion_of
    in
    let body =
      ExtTerm.subst eqsubst
      @@ ExtTerm.and_of
           [
             ExtTerm.neg_of @@ OptimalityChecker.apply_pred theta p w;
             ExtTerm.mk_var_app pdom_0 @@ w @ args_y;
             ExtTerm.and_of pfapps;
           ]
    in
    let bodys =
      if p_has_trans_clause then [ body ]
      else
        List.map special_pfappss ~f:(fun phis ->
            ExtTerm.and_of @@ (body :: phis))
    in
    let head =
      ExtTerm.rename p_y_subst
      @@
      if Map.Poly.mem bwd_theta p_y then
        ExtTerm.or_of
          [ OptimalityChecker.apply_pred bwd_theta p_y args_y; head ]
      else head
    in
    let constrs =
      List.map bodys ~f:(fun body ->
          let body = ExtTerm.simplify_formula exi_senv uni_senv body in
          ExtTerm.rename p_y_subst @@ ExtTerm.imply_of body head)
    in
    Debug.print_log ~tag:"backward_constrs:"
    @@ lazy
         ("\n"
         ^ String.concat_map_list ~sep:"\n" constrs ~f:(fun constr ->
               "*** " ^ ExtTerm.str_of_formula exi_senv uni_senv constr));
    let kind_map =
      List.unzip pfs_senv |> fst
      |> List.map ~f:(fun pf -> (pf, Kind.FN))
      |> Map.Poly.of_alist_exn
    in
    let tvs = ExtTerm.fvs_of (ExtTerm.and_of constrs) in
    let uni_senv = Map.Poly.filter_keys uni_senv ~f:(Set.mem tvs) in
    (exi_senv, kind_map, (uni_senv, (p_y, constrs)))

  let forward_of p
      (idx_map : (tvar, (int * tvar) * Sort.t list * tvar) Map.Poly.t) theta w
      (_, w_sorts, _) exi_senv i (uni_senv, ps, ns, phi) =
    assert (Set.is_empty ps);
    Debug.print_log ~tag:"forward_of"
    @@ lazy (Clause.str_of exi_senv (uni_senv, ps, ns, phi));
    let p_xs, arg_xs =
      Set.to_list ns |> List.map ~f:Term.let_apps
      |> List.map ~f:(fun (p, args) -> (fst @@ Term.let_var p, args))
      |> List.unzip
    in
    let idxs, sortss, pdoms =
      List.unzip3 @@ List.map p_xs ~f:(Map.Poly.find_exn idx_map)
    in
    let pf = OptimalityChecker.pn (Tvar "FNf") i in
    let pfs_senv, pfapps =
      List.zip3_exn idxs arg_xs sortss
      |> List.concat_mapi ~f:(fun j ((_, p_x), arg_xs, sorts) ->
             List.mapi (List.zip_exn arg_xs sorts) ~f:(fun k (x, s) ->
                 let fnargs = w in
                 let fnret = x in
                 let pfi =
                   OptimalityChecker.pnc
                     (OptimalityChecker.pnt (OptimalityChecker.pn pf j) p_x)
                     k
                 in
                 let pfi_sort = Sort.mk_fun @@ w_sorts @ [ s; ExtTerm.SBool ] in
                 ( (pfi, pfi_sort),
                   ( (pfi, ()),
                     ( (None, ExtTerm.mk_var_app pfi @@ fnargs @ [ fnret ]),
                       (fnargs, fnret) ) ) )))
      |> List.unzip
    in
    let exi_senv =
      Map.force_merge_list
        [
          exi_senv;
          Map.Poly.of_alist_exn
          @@ List.dedup_and_sort ~compare:Stdlib.compare pfs_senv;
        ]
    in
    let bound =
      List.map (List.concat arg_xs) ~f:(fun t ->
          let v, _ = ExtTerm.let_var t in
          (v, Map.Poly.find_exn uni_senv v))
      |> Map.Poly.of_alist_exn
    in
    let fvs, pure_phi =
      OptimalityChecker.apply_qelim_on_pure_formula bound exi_senv uni_senv
      @@ ExtTerm.neg_of phi
    in
    Debug.print_log ~tag:"pure_formula"
    @@ lazy (ExtTerm.str_of_formula exi_senv uni_senv pure_phi);
    assert (List.is_empty fvs);
    let sol_apply_map =
      List.mapi (List.zip_exn p_xs arg_xs) ~f:(fun j (p_x, args) ->
          let phi =
            if Stdlib.(p_x = p) then
              ExtTerm.or_of
                [
                  OptimalityChecker.apply_pred theta p_x args;
                  OptimalityChecker.eqs_of w_sorts w args;
                ]
            else if term_in_other_sol then
              OptimalityChecker.apply_pred theta p_x args
            else ExtTerm.mk_bool false
          in
          (j, (phi, ExtTerm.mk_var_app (List.nth_exn pdoms j) @@ w @ args)))
      |> Set.Poly.of_list |> Set.to_list |> Map.Poly.of_alist_exn
    in
    let pure_phi, sol_apply_map, pfapps, eqsubst =
      OptimalityChecker.filter_pfapps exi_senv uni_senv pfapps pure_phi
        sol_apply_map
    in
    let head =
      ExtTerm.subst eqsubst @@ ExtTerm.and_of @@ List.cons pure_phi
      @@ List.mapi (List.zip_exn p_xs arg_xs) ~f:(fun j (_, _) ->
             let app_phi, dom_phi = Map.Poly.find_exn sol_apply_map j in
             Debug.print
             @@ lazy
                  (sprintf "check %s => %s"
                     (ExtTerm.str_of_formula exi_senv uni_senv pure_phi)
                     (ExtTerm.str_of_formula exi_senv uni_senv app_phi));
             match
               OptimalityChecker.check exi_senv uni_senv pure_phi app_phi
             with
             | Some true -> ExtTerm.mk_bool true
             | Some false -> dom_phi
             | None -> ExtTerm.or_of [ app_phi; dom_phi ])
    in
    let head_fvs = ExtTerm.fvs_of head in
    let pfapps =
      List.filter_map pfapps ~f:(fun (_, ((_, term), (_, sol))) ->
          let v, _ = ExtTerm.let_var sol in
          if Set.mem head_fvs v then Some term else None)
    in
    let body =
      ExtTerm.simplify_formula exi_senv uni_senv
      @@ ExtTerm.and_of
      @@ ((ExtTerm.neg_of @@ OptimalityChecker.apply_pred theta p w) :: pfapps)
    in
    let kind_map =
      List.unzip pfs_senv |> fst
      |> List.map ~f:(fun pf -> (pf, Kind.FN))
      |> Map.Poly.of_alist_exn
    in
    let constr = ExtTerm.imply_of body head in
    Debug.print_log ~tag:"forward_clause:"
    @@ lazy (ExtTerm.str_of_formula exi_senv uni_senv constr);
    let tvs = ExtTerm.fvs_of constr in
    let uni_senv = Map.Poly.filter_keys uni_senv ~f:(Set.mem tvs) in
    (exi_senv, kind_map, (uni_senv, constr))

  let backward_clauses_of_bwd_theta p pvars idx_map w exi_senv uni_senv
      bwd_theta theta trans_cls =
    let has_trans_clause p =
      List.exists trans_cls ~f:(OptimalityChecker.head_is p)
    in
    List.filter_map pvars ~f:(fun (p_y, _) ->
        if has_trans_clause p_y || (not @@ Map.Poly.mem bwd_theta p_y) then None
        else
          let sol = Map.Poly.find_exn bwd_theta p_y in
          let _, _, pdom_0 = Map.Poly.find_exn idx_map p_y in
          let param_senv, pure_phi = ExtTerm.let_lam sol in
          let args_y =
            List.map param_senv ~f:(fun (v, _) -> ExtTerm.mk_var v)
          in
          let body =
            ExtTerm.and_of
              [
                ExtTerm.neg_of @@ OptimalityChecker.apply_pred theta p w;
                ExtTerm.mk_var_app pdom_0 @@ w @ args_y;
              ]
          in
          let constr = ExtTerm.imply_of body pure_phi in
          let uni_senv =
            Map.force_merge uni_senv (Map.Poly.of_alist_exn param_senv)
          in
          Debug.print_log ~tag:"backward_clauses_of_bwd_theta"
          @@ lazy (ExtTerm.str_of_formula exi_senv uni_senv constr);
          Some (exi_senv, Map.Poly.empty, (uni_senv, (p_y, [ constr ]))))

  let backward_clauses_of p pvars pysenv
      (idx_map : (tvar, (int * tvar) * Sort.t list * tvar) Map.Poly.t) nwf theta
      w winfo exi_senv uni_senv defs =
    let p_has_trans_clause =
      List.exists defs ~f:(OptimalityChecker.head_is p)
    in
    let _, wsorts, _ = winfo in
    let trans_cls, start_cls =
      List.partition_tf defs ~f:(fun (_, _, ns, _) -> Fn.non Set.is_empty ns)
    in
    let init_bwd_theta = init_bwd_theta_of w p exi_senv theta in
    let bwd_theta =
      OptimalityChecker.bwd_theta_of ~init:init_bwd_theta exi_senv start_cls
    in
    let init_clauses =
      backward_clauses_of_bwd_theta p pvars idx_map w exi_senv uni_senv
        bwd_theta theta trans_cls
    in
    let exi_senv, kind_map, uni_senv, phis =
      if List.is_empty defs && List.is_empty init_clauses then
        (exi_senv, Map.Poly.empty, uni_senv, [])
      else
        List.mapi trans_cls
          ~f:
            (backward_of p p_has_trans_clause pysenv bwd_theta idx_map nwf theta
               w winfo exi_senv)
        |> List.append init_clauses |> List.unzip3
        |> fun (exi_senvs, kind_maps, phis) ->
        let uni_senvs, phis = List.unzip phis in
        ( Map.force_merge_list (exi_senv :: exi_senvs),
          Map.force_merge_list kind_maps,
          Map.force_merge_list (uni_senv :: uni_senvs)
            ~catch_dup:(fun (key, data1, data2) ->
              print_endline
              @@ sprintf "%s : %s != %s" (name_of_tvar key)
                   (ExtTerm.str_of_sort data1)
                   (ExtTerm.str_of_sort data2)),
          phis )
    in
    let exi_senv, phis =
      List.classify (fun (p1, _) (p2, _) -> Stdlib.(p1 = p2)) phis
      |> List.mapi ~f:(fun i phis ->
             let p = fst @@ List.hd_exn phis in
             let phis = List.map phis ~f:snd in
             let args, sargs = List.unzip @@ Map.Poly.find_exn pysenv p in
             let args = List.map args ~f:ExtTerm.mk_var in
             OptimalityChecker.mk_tseitin_pred_clause (i + 1)
               (w @ args, wsorts @ sargs)
               exi_senv phis)
      |> List.unzip
      |> fun (exi_senvs, phiss) ->
      (Map.force_merge_list exi_senvs, List.concat phiss)
    in
    Debug.print_log ~tag:"backward constrs"
    @@ lazy
         (sprintf "\n*** %s\n"
         @@ String.concat_map_list ~sep:"\n*** " phis
              ~f:(ExtTerm.str_of_formula exi_senv uni_senv));
    ( exi_senv,
      kind_map,
      OptimalityChecker.to_cnf_clauses exi_senv uni_senv
      @@ ExtTerm.and_of @@ phis )

  let forward_clauses_of p
      (idx_map : (tvar, (int * tvar) * Sort.t list * tvar) Map.Poly.t) theta w
      winfo exi_senv uni_senv goals =
    let _, wsorts, _ = winfo in
    let exi_senv, kind_map, uni_senv, phis =
      if List.is_empty goals then
        ( exi_senv,
          Map.Poly.empty,
          uni_senv,
          [ [ OptimalityChecker.apply_pred theta p w ] ] )
      else
        List.mapi goals ~f:(forward_of p idx_map theta w winfo exi_senv)
        |> List.unzip3
        |> fun (exi_senvs, kind_maps, phis) ->
        let uni_senvs, phis = List.unzip phis in
        ( Map.force_merge_list exi_senvs,
          Map.force_merge_list kind_maps,
          Map.force_merge_list (uni_senv :: uni_senvs),
          List.map phis ~f:List.return )
    in
    let exi_senv, phis =
      OptimalityChecker.mk_tseitin_pred_clause 0 (w, wsorts) exi_senv @@ phis
    in
    Debug.print_log ~tag:"forward constrs"
    @@ lazy
         (sprintf "\n*** %s\n"
         @@ String.concat_map_list ~sep:"\n*** " phis
              ~f:(ExtTerm.str_of_formula exi_senv uni_senv));
    let phi = ExtTerm.and_of phis in
    (* let body = ExtTerm.neg_of @@ apply_pred theta p w in
       let phi = ExtTerm.imply_of body head in *)
    Debug.print_log ~tag:"forward_formula:"
    @@ lazy (ExtTerm.str_of_formula exi_senv uni_senv phi);
    (exi_senv, kind_map, OptimalityChecker.to_cnf_clauses exi_senv uni_senv phi)

  let check ?(only_simple = false) (messenger, id) p pcsp senv theta =
    let pcsp = OptimalityChecker.elim_clauses pcsp in
    OptimalityChecker.set_id id;
    Debug.set_id id;
    if OptimalityChecker.simple_check ~is_max:true p senv theta then
      CHCOpt.Problem.OptSat theta
    else if only_simple then CHCOpt.Problem.Unknown
    else
      let pvars = OptimalityChecker.pvars_of p senv in
      Debug.print_log ~tag:"pvar id"
      @@ lazy
           (sprintf "%s"
           @@ String.concat_mapi_list ~sep:"," pvars ~f:(fun i (var, _) ->
                  sprintf "%d:%s" i @@ name_of_tvar var));
      let idxs = OptimalityChecker.idxs_of pvars in
      let pysenv = OptimalityChecker.pysenv_of pvars in
      let idx_map = Map.Poly.of_alist_exn idxs in
      let pinfo = Map.Poly.find_exn idx_map p in
      let (pi, _), sorts_p, _ = pinfo in
      let nwf = Kind.create_nwf (Tvar (sprintf "WF%d" pi)) sorts_p in
      List.iter idxs ~f:(fun (p, (_, sorts, _)) -> Kind.set_tag nwf p sorts);
      let kind_map = Kind.kind_map_of_nwf nwf in
      let wsenv = mk_fresh_sort_env_list sorts_p in
      let w = List.map wsenv ~f:(fun (v, _) -> ExtTerm.mk_var v) in
      let uni_senv =
        Map.Poly.fold pysenv ~init:wsenv ~f:(fun ~key:_ ~data:pys acc ->
            pys @ acc)
        |> Map.Poly.of_alist_exn
      in
      let pdoms =
        List.map idxs ~f:(fun (p, (_, sorts, pdom)) ->
            (p, (pdom, Sort.mk_fun @@ sorts_p @ sorts @ [ ExtTerm.SBool ])))
        |> Map.Poly.of_alist_exn
      in
      let pdom_senv =
        Map.Poly.to_alist pdoms |> List.unzip |> snd
        |> List.dedup_and_sort ~compare:Stdlib.compare
        |> Map.Poly.of_alist_exn
      in
      let exi_senv = Map.force_merge pdom_senv senv in
      let pcsp =
        PCSP.Problem.clauses_of @@ PCSP.Problem.merge_clauses
        @@ PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf pcsp
        |> Set.Poly.map ~f:(fun (params, ps, ns, phi) ->
               (Map.force_merge uni_senv params, ps, ns, phi))
        |> PCSP.Problem.of_clauses ~params:(PCSP.Problem.params_of pcsp)
      in
      Debug.print_log ~tag:"pcsp" @@ lazy ("\n" ^ PCSP.Problem.str_of pcsp);
      let defs = OptimalityChecker.defs_of pcsp in
      let goals = OptimalityChecker.goals_of pcsp in
      let exi_senv1, kind_map1, bwd_clauses =
        backward_clauses_of p pvars pysenv idx_map nwf theta w pinfo exi_senv
          uni_senv defs
      in
      let exi_senv2, kind_map2, fwd_clauses =
        forward_clauses_of p idx_map theta w pinfo exi_senv uni_senv goals
      in
      (* let default_clauses = default_clause_of p theta w pinfo exi_senv uni_senv in *)
      let kind_map = Map.force_merge_list [ kind_map; kind_map1; kind_map2 ] in
      let exi_senv = Map.force_merge exi_senv1 exi_senv2 in
      let clauses =
        Set.union bwd_clauses fwd_clauses
        (* |> Set.union default_clauses *)
        (* |> Set.concat_map ~f:(simplify_fnpvs exi_senv fnpvs) *)
      in
      let params =
        PCSP.Params.make ~kind_map
          ~fenv:(PCSP.Problem.fenv_of pcsp)
          ~dtenv:(PCSP.Problem.dtenv_of pcsp)
          ~id ~messenger exi_senv
      in
      let pcsp' =
        clauses
        |> PCSP.Problem.of_clauses ~params
        |> PCSP.Problem.formulas_of
        |> PCSP.Problem.of_formulas ~params
        (* |> PCSP.Problem.to_nnf *)
        (* |> PCSP.Problem.to_cnf *)
      in
      let bpvs =
        Map.key_set exi_senv |> Set.filter ~f:OptimalityChecker.is_ptseitin
        |> fun _ -> Set.Poly.empty
      in
      (* Solver.reset (); *)
      let (module Solver : PCSPSolver.Solver.SolverType) = pcsp_solver_of p in
      match Solver.solve ~bpvs pcsp' with
      | Ok (PCSP.Problem.Sat _, _) -> CHCOpt.Problem.OptSat theta
      | _ -> CHCOpt.Problem.Unknown
end

let make config =
  (module Make (struct
    let config = config
  end) : OptimalityChecker.OptimalityCheckerType)
