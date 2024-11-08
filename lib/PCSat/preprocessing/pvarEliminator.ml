open Core
open Common
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

module Make
    (Verbose : Debug.Config.ConfigType)
    (Config : sig
      val resolution_threshold : int
      val propagate_lb_ub : bool
    end) =
struct
  module Debug = Debug.Make (Verbose)

  let id : int option ref = ref None
  let eliminated_pvars = ref Map.Poly.empty

  (* *)
  let resolve_solution_of pv exi_senv clauses_pos =
    let is_resolved atm = Stdlib.(pv = Atom.pvar_of atm) in
    let args =
      Map.Poly.find_exn exi_senv (Ident.pvar_to_tvar pv)
      |> Logic.Sort.args_of
      |> List.map ~f:(Logic.ExtTerm.to_old_sort >> Term.mk_fresh_var)
    in
    let eqs, param_senvs, phis =
      List.unzip3
      @@ List.map clauses_pos ~f:(fun (param_senv, ps, ns, phi) ->
             let _, _, args0, _ =
               Atom.let_pvar_app @@ Set.find_exn ~f:is_resolved ps
             in
             let eq =
               Formula.and_of @@ List.map2_exn args args0 ~f:Formula.eq
             in
             let ps' =
               Set.filter ps ~f:(Atom.pvar_of >> Stdlib.( <> ) pv)
               |> Set.to_list
               |> List.map ~f:Formula.mk_atom
             in
             let ns' =
               Set.to_list ns |> List.map ~f:(Formula.mk_atom >> Formula.mk_neg)
             in
             let param_senv' =
               Map.Poly.to_alist param_senv |> Logic.to_old_sort_env_list
             in
             ( eq,
               param_senv',
               Formula.mk_neg @@ Formula.or_of @@ ps' @ ns' @ [ phi ] ))
    in
    let params =
      List.map args
        ~f:(Term.let_var >> fst >> Pair.map_snd Logic.ExtTerm.of_old_sort)
    in
    Logic.ExtTerm.mk_lambda params
    @@ Logic.ExtTerm.of_old_formula
    @@ (fun ret ->
         Debug.print
         @@ lazy
              (sprintf "[resolve_solution_of] \n%s (%s) := %s"
                 (Ident.name_of_pvar pv)
                 (String.concat_map_list ~sep:"," args ~f:Term.str_of)
                 (Formula.str_of ret));
         ret)
    @@ Z3Smt.Z3interface.qelim ~id:!id ~fenv:(LogicOld.get_fenv ())
    @@ Formula.exists (List.concat param_senvs)
    @@ Evaluator.simplify @@ Formula.and_of @@ eqs @ phis
  (* *)

  let resolve qelim exi_senv pv clauses =
    Debug.print @@ lazy (sprintf "eliminating %s" @@ Ident.name_of_pvar pv);
    let is_resolved atm = Stdlib.(pv = Atom.pvar_of atm) in
    let clauses_pos, clauses_neg, clauses_rest =
      Set.partition3_map clauses ~f:(fun ((_, ps, ns, _) as cl) ->
          if Set.exists ps ~f:is_resolved then `Fst cl
          else if Set.exists ns ~f:is_resolved then `Snd cl
          else `Trd cl)
    in
    (* let sol_of_pv = resolve_solution_of pv exi_senv clauses_pos in
       eliminated_pvars :=
       Map.Poly.add_exn !eliminated_pvars ~key:(Ident.pvar_to_tvar pv) ~data:sol_of_pv; *)
    let clauses_pos_lin, clauses_pos_nonlin =
      Set.partition_tf clauses_pos ~f:(fun (_, ps, _, _) ->
          Set.count ps ~f:is_resolved = 1)
    in
    let clauses_neg_lin, clauses_neg_nonlin =
      Set.partition_tf clauses_neg ~f:(fun (_, _, ns, _) ->
          Set.count ns ~f:is_resolved = 1)
    in
    Debug.print
    @@ lazy
         (sprintf
            "#rest %d, #poslin: %d, #posnonlin: %d, #neglin: %d, #negnonlin: %d"
            (Set.length clauses_rest)
            (Set.length clauses_pos_lin)
            (Set.length clauses_pos_nonlin)
            (Set.length clauses_neg_lin)
            (Set.length clauses_neg_nonlin));
    let cls =
      Set.union clauses_rest
      @@ ClauseSetOld.simplify (Map.key_set exi_senv)
           (Z3Smt.Z3interface.is_valid ~id:!id (LogicOld.get_fenv ()))
      @@ Set.concat_map ~f:(fun cl ->
             let senv, phi =
               let senv, phi = ClauseOld.to_formula cl in
               (* ToDo: the following can be a bottle neck *)
               qelim (senv, Normalizer.normalize @@ Evaluator.simplify phi)
             in
             Set.Poly.map ~f:(fun (ps, ns, phi) -> (senv, ps, ns, phi))
             @@ Formula.cnf_of Logic.(to_old_sort_env_map exi_senv)
             @@ Normalizer.normalize @@ Evaluator.simplify phi)
      @@ Set.Poly.map ~f:(fun (senv, ps, ns, phis) ->
             (senv, ps, ns, Formula.or_of phis))
      @@ Set.Poly.union_list
      @@ [
           Set.cartesian_map clauses_pos_lin clauses_neg_lin
             ~f:(fun (senv1, ps1, ns1, phi1) ncl ->
               (*print_string "ll:"; Out_channel.flush stdout;*)
               let ps11, ps12 = Set.partition_tf ps1 ~f:is_resolved in
               Set.fold ps11 ~init:(senv1, ps12, ns1, [ phi1 ])
                 ~f:(fun (senv, ps, ns, phis) -> function
                 | Atom.App (_, ts1, _) -> (
                     let senv2, ps2, ns2, phi2 = ClauseOld.refresh_tvar ncl in
                     let ns21, ns22 = Set.partition_tf ns2 ~f:is_resolved in
                     match Set.choose ns21 with
                     | Some (Atom.App (_, ts2, _)) ->
                         ( Map.force_merge senv senv2,
                           Set.union ps ps2,
                           Set.union ns ns22,
                           phis @ (phi2 :: List.map2_exn ts1 ts2 ~f:Formula.neq)
                         )
                     | _ -> assert false)
                 | _ -> assert false));
           Set.concat_map clauses_pos_nonlin ~f:(fun (senv1, ps1, ns1, phi1) ->
               let ps11, ps12 = Set.partition_tf ps1 ~f:is_resolved in
               Set.fold ps11
                 ~init:(Set.Poly.singleton (senv1, ps12, ns1, [ phi1 ]))
                 ~f:(fun acc -> function
                   | Atom.App (_, ts1, _) ->
                       Set.concat_map acc ~f:(fun (senv, ps, ns, phis) ->
                           Set.Poly.map clauses_neg_lin ~f:(fun ncl ->
                               (*print_string "nl:"; Out_channel.flush stdout;*)
                               let senv2, ps2, ns2, phi2 =
                                 ClauseOld.refresh_tvar ncl
                               in
                               let ns21, ns22 =
                                 Set.partition_tf ns2 ~f:is_resolved
                               in
                               match Set.choose ns21 with
                               | Some (Atom.App (_, ts2, _)) ->
                                   ( Map.force_merge senv senv2,
                                     Set.union ps ps2,
                                     Set.union ns ns22,
                                     phis
                                     @ phi2
                                       :: List.map2_exn ts1 ts2 ~f:Formula.neq
                                   )
                               | _ -> assert false))
                   | _ -> assert false));
           Set.concat_map clauses_neg_nonlin ~f:(fun (senv1, ps1, ns1, phi1) ->
               let ns11, ns12 = Set.partition_tf ns1 ~f:is_resolved in
               Set.fold ns11
                 ~init:(Set.Poly.singleton (senv1, ps1, ns12, [ phi1 ]))
                 ~f:(fun acc -> function
                   | Atom.App (_, ts1, _) ->
                       Set.concat_map acc ~f:(fun (senv, ps, ns, phis) ->
                           Set.Poly.map clauses_pos_lin ~f:(fun pcl ->
                               (*print_string "ln:"; Out_channel.flush stdout;*)
                               let senv2, ps2, ns2, phi2 =
                                 ClauseOld.refresh_tvar pcl
                               in
                               let ps21, ps22 =
                                 Set.partition_tf ps2 ~f:is_resolved
                               in
                               match Set.choose ps21 with
                               | Some (Atom.App (_, ts2, _)) ->
                                   ( Map.force_merge senv senv2,
                                     Set.union ps ps22,
                                     Set.union ns ns2,
                                     phis
                                     @ phi2
                                       :: List.map2_exn ts1 ts2 ~f:Formula.neq
                                   )
                               | _ -> assert false))
                   | _ -> assert false));
         ]
    in
    (*Debug.print @@ lazy "done";
      Set.iter cls ~f:(fun c -> Debug.print @@ lazy ("  " ^ ClauseOld.str_of c));*)
    cls

  let rec elim_one_side_unbounded_pvars exi_senv eliminable_pvs clauses =
    let pvs =
      Set.Poly.filter_map
        (fst @@ ClauseSetOld.count_pvar_apps eliminable_pvs clauses)
        ~f:(fun (pvar, (_dc, pc, nc)) ->
          if (*dc = 0 &&*) pc = 0 (* pvar can be false *) then (
            Debug.print
            @@ lazy
                 (sprintf "%s is assigned false because there is no LB"
                 @@ Ident.name_of_pvar pvar);
            let params =
              mk_fresh_sort_env_list @@ Logic.Sort.args_of
              @@ Map.Poly.find_exn exi_senv (Ident.pvar_to_tvar pvar)
            in
            let phi =
              Logic.Term.mk_lambda params @@ Logic.ExtTerm.mk_bool false
            in
            eliminated_pvars :=
              Map.Poly.add_exn !eliminated_pvars ~key:(Ident.pvar_to_tvar pvar)
                ~data:phi;
            Some pvar)
          else if (*dc = 0 &&*) nc = 0 (* pvar can be true *) then (
            Debug.print
            @@ lazy
                 (sprintf "%s is assigned true because there is no UB"
                 @@ Ident.name_of_pvar pvar);
            let params =
              mk_fresh_sort_env_list @@ Logic.Sort.args_of
              @@ Map.Poly.find_exn exi_senv (Ident.pvar_to_tvar pvar)
            in
            let phi =
              Logic.Term.mk_lambda params @@ Logic.ExtTerm.mk_bool true
            in
            eliminated_pvars :=
              Map.Poly.add_exn !eliminated_pvars ~key:(Ident.pvar_to_tvar pvar)
                ~data:phi;
            Some pvar)
          else None)
    in
    let clauses' =
      Set.filter clauses ~f:(fun (_, ps, ns, _) ->
          Set.is_empty
          @@ Set.inter pvs (Set.Poly.map (Set.union ps ns) ~f:Atom.pvar_of))
    in
    if Set.eqlen clauses clauses' then clauses'
    else elim_one_side_unbounded_pvars exi_senv eliminable_pvs clauses'

  let subst_preds unknowns psub cls =
    let cls1, cls2 =
      Set.partition_map cls ~f:(fun cl ->
          let cl, changed = ClauseOld.subst_preds psub cl in
          if changed then Second cl else First cl)
    in
    ( cls1,
      Set.Poly.filter_map cls2
        ~f:
          (ClauseOld.simplify unknowns
             (Z3Smt.Z3interface.is_valid ~id:!id (LogicOld.get_fenv ()))) )

  let lbs_ubs_of exi_senv clauses =
    Pair.map (Set.Poly.filter_map ~f:Fn.id) (Set.Poly.filter_map ~f:Fn.id)
    @@ Set.unzip
    @@ Set.Poly.map clauses ~f:(fun (_, ps, ns, phi) ->
           Debug.print @@ lazy (sprintf "[lbs_ubs_of] %s" @@ Formula.str_of phi);
           (* assume that [phi] is alpha-renamed *)
           let lenv = Set.of_map @@ Formula.let_sort_env_of phi in
           (* let lenv = Set.Poly.empty in *)
           if Set.is_singleton ps && Set.is_empty ns then
             match Set.choose ps with
             | Some (Atom.App (Predicate.Var (pvar, sorts), ts, _)) ->
                 let xs = mk_fresh_sort_env_list sorts in
                 let phi' =
                   Formula.or_of
                   @@ phi
                      :: List.map2_exn ~f:Formula.neq ts (Term.of_sort_env xs)
                 in
                 let ys =
                   Set.diff
                     (Set.diff (Formula.sort_env_of phi') (Set.Poly.of_list xs))
                     lenv
                   |> Set.filter
                        ~f:(fst >> Set.mem (Map.key_set exi_senv) >> not)
                 in
                 let senv =
                   Map.of_set_exn @@ Logic.of_old_sort_env_set
                   @@ Set.union (Set.Poly.of_list xs) ys
                 in
                 Debug.print
                 @@ lazy
                      (sprintf "[lbs_ubs_of] senv: %s"
                      @@ Logic.(
                           str_of_sort_env_list ExtTerm.str_of_sort
                           @@ Map.Poly.to_alist senv));
                 (* (exists ys. not phi /\ xs = ts) => pvar(xs) *)
                 let lb =
                   Formula.exists (Set.to_list ys)
                   @@ Formula.elim_let_equi false
                   @@ Normalizer.normalize_let ~rename:true
                   @@ Formula.mk_neg @@ snd
                   @@ Qelim.qelim_old
                        (Map.Poly.of_alist_exn @@ Logic.of_old_sort_env_list xs)
                        exi_senv (senv, phi')
                 in
                 Debug.print
                 @@ lazy
                      (sprintf "LB of %s(%s): %s" (Ident.name_of_pvar pvar)
                         (str_of_sort_env_list LogicOld.Term.str_of_sort xs)
                         (Formula.str_of lb));
                 (Some (pvar, (xs, lb)), None)
             | _ -> assert false
           else if Set.is_empty ps && Set.is_singleton ns then
             match Set.choose ns with
             | Some (Atom.App (Predicate.Var (pvar, sorts), ts, _)) ->
                 let xs = mk_fresh_sort_env_list sorts in
                 let phi' =
                   Formula.or_of
                   @@ phi
                      :: List.map2_exn ~f:Formula.neq ts (Term.of_sort_env xs)
                 in
                 let ys =
                   Set.diff
                     (Set.diff (Formula.sort_env_of phi') (Set.Poly.of_list xs))
                     lenv
                   |> Set.filter
                        ~f:(fst >> Set.mem (Map.key_set exi_senv) >> not)
                 in
                 let senv =
                   Map.of_set_exn @@ Logic.of_old_sort_env_set
                   @@ Set.union (Set.Poly.of_list xs) ys
                 in
                 Debug.print
                 @@ lazy
                      (sprintf "[lbs_ubs_of] senv: %s"
                      @@ Logic.(
                           str_of_sort_env_list ExtTerm.str_of_sort
                           @@ Map.Poly.to_alist senv));
                 (* pvar(xs) => (forall ys. xs = ts => phi) *)
                 let ub =
                   Formula.forall (Set.to_list ys)
                   @@ Formula.elim_let_equi true
                   @@ Normalizer.normalize_let ~rename:true
                   @@ snd
                   @@ Qelim.qelim_old
                        (Map.Poly.of_alist_exn @@ Logic.of_old_sort_env_list xs)
                        exi_senv (senv, phi')
                 in
                 Debug.print
                 @@ lazy
                      (sprintf "UB of %s(%s): %s" (Ident.name_of_pvar pvar)
                         (str_of_sort_env_list LogicOld.Term.str_of_sort xs)
                         (Formula.str_of ub));
                 (None, Some (pvar, (xs, ub)))
             | _ -> assert false
           else (None, None))

  let clause_of_lb pvar (senv, phi) =
    ( Map.Poly.of_alist_exn @@ Logic.of_old_sort_env_list senv,
      Set.Poly.singleton @@ Atom.pvar_app_of_senv pvar senv,
      Set.Poly.empty,
      Formula.mk_neg phi )

  let clause_of_ub pvar (senv, phi) =
    ( Map.Poly.of_alist_exn @@ Logic.of_old_sort_env_list senv,
      Set.Poly.empty,
      Set.Poly.singleton @@ Atom.pvar_app_of_senv pvar senv,
      phi )

  let or_preds params preds =
    Formula.or_of @@ Set.to_list
    @@ Set.Poly.map preds ~f:(fun (params', phi) ->
           Formula.rename (tvar_map_of_sort_env_list params' params) phi)

  let and_preds params preds =
    Formula.and_of @@ Set.to_list
    @@ Set.Poly.map preds ~f:(fun (params', phi) ->
           Formula.rename (tvar_map_of_sort_env_list params' params) phi)

  let elim_pvars_with_lb_ub exi_senv eliminable_pvs clauses =
    let cls = ref Set.Poly.empty in
    let psub =
      let lbs, ubs = lbs_ubs_of exi_senv clauses in
      Map.of_set_exn
      @@ Set.Poly.filter_map eliminable_pvs ~f:(fun pvar ->
             let pvar_lbs =
               Set.Poly.filter_map lbs ~f:(fun (pvar', lb) ->
                   if Stdlib.(pvar = pvar') then Some lb else None)
             in
             let pvar_ubs =
               Set.Poly.filter_map ubs ~f:(fun (pvar', ub) ->
                   if Stdlib.(pvar = pvar') then Some ub else None)
             in
             let pvar_lbs_ubs = Set.union pvar_lbs pvar_ubs in
             if Set.is_empty pvar_lbs_ubs then None
             else
               let params, _ = Set.choose_exn pvar_lbs_ubs in
               let lb = or_preds params pvar_lbs in
               let ok_lb =
                 Set.(
                   is_empty @@ inter (Formula.fvs_of lb) (Map.key_set exi_senv))
               in
               let ub = and_preds params pvar_ubs in
               let ok_ub =
                 Set.(
                   is_empty @@ inter (Formula.fvs_of ub) (Map.key_set exi_senv))
               in
               if
                 ok_lb
                 && Z3Smt.Z3interface.is_valid ~id:!id (LogicOld.get_fenv ()) lb
               then (
                 Debug.print
                 @@ lazy
                      (sprintf "%s is assigned true because LB is true"
                      @@ Ident.name_of_pvar pvar);
                 let phi =
                   Logic.(
                     Term.mk_lambda (of_old_sort_env_list params)
                     @@ ExtTerm.mk_bool true)
                 in
                 eliminated_pvars :=
                   Map.Poly.add_exn !eliminated_pvars
                     ~key:(Ident.pvar_to_tvar pvar) ~data:phi;
                 Some
                   ( pvar,
                     (params, Formula.mk_true (), Formula.mk_false (), false) ))
               else if
                 ok_ub
                 && Z3Smt.Z3interface.is_valid ~id:!id (LogicOld.get_fenv ())
                    @@ Formula.mk_neg ub
               then (
                 Debug.print
                 @@ lazy
                      (sprintf "%s is assigned false because UB is false"
                      @@ Ident.name_of_pvar pvar);
                 let phi =
                   Logic.(
                     Term.mk_lambda (of_old_sort_env_list params)
                     @@ ExtTerm.mk_bool false)
                 in
                 eliminated_pvars :=
                   Map.Poly.add_exn !eliminated_pvars
                     ~key:(Ident.pvar_to_tvar pvar) ~data:phi;
                 Some
                   ( pvar,
                     (params, Formula.mk_false (), Formula.mk_true (), false) ))
               else if
                 Set.exists pvar_lbs ~f:(snd >> Formula.is_exists)
                 || Set.exists pvar_ubs ~f:(snd >> Formula.is_forall)
               then None
               else if
                 ok_lb && ok_ub
                 && Z3Smt.Z3interface.is_valid ~id:!id (LogicOld.get_fenv ())
                    @@ Formula.mk_iff lb ub
               then (
                 Debug.print
                 @@ lazy
                      (sprintf
                         "%s is assigned %s because LB and UB are equivalent"
                         (Ident.name_of_pvar pvar)
                      @@ Formula.str_of lb);
                 let phi =
                   Logic.(
                     Term.mk_lambda (of_old_sort_env_list params)
                     @@ ExtTerm.of_old_formula lb (*ToDo: ub is ignored*))
                 in
                 eliminated_pvars :=
                   Map.Poly.add_exn !eliminated_pvars
                     ~key:(Ident.pvar_to_tvar pvar) ~data:phi;
                 Some (pvar, (params, lb, Formula.mk_neg ub, false)))
               else if Config.propagate_lb_ub then (
                 Debug.print
                 @@ lazy
                      (sprintf "LB and UB of %s are propagated"
                      @@ Ident.name_of_pvar pvar);
                 (*ToDo: this may widen the solution space?*)
                 cls :=
                   Set.Poly.union_list
                     [
                       Set.Poly.map ~f:(clause_of_lb pvar) pvar_lbs;
                       Set.Poly.map ~f:(clause_of_ub pvar) pvar_ubs;
                       !cls;
                     ];
                 Some (pvar, (params, lb, Formula.mk_neg ub, true)))
               else None)
    in
    let cls1, cls2 = subst_preds (Map.key_set exi_senv) psub clauses in
    Set.Poly.union_list [ !cls; cls1; cls2 ]

  let rec elim_pvars_by_resolution qelim exi_senv eliminable_pvs clauses =
    let pvs, dc_pvs = ClauseSetOld.count_pvar_apps eliminable_pvs clauses in
    let pvs_info1, pvs_info2 =
      Set.Poly.filter_map pvs ~f:(fun (pvar, (dc, pc, nc)) ->
          if dc = 0 && not (Set.mem dc_pvs pvar) then
            let pn = pc * nc in
            if pn <= Config.resolution_threshold then
              Some
                ( pvar,
                  List.length @@ Logic.Sort.args_of
                  @@ Map.Poly.find_exn exi_senv (Ident.pvar_to_tvar pvar),
                  (pc, nc, pn) )
            else None
          else None)
      |> Set.partition_tf ~f:(fun (pvar, _, (_, _, _)) ->
             Set.fold clauses ~init:(true, true)
               ~f:(fun (p, n) (senv, pos, neg, _phi) ->
                 if p || n then
                   match
                     Set.find pos ~f:(Atom.pvs_of >> Fn.flip Set.mem pvar)
                   with
                   | Some atm ->
                       ( p
                         && Set.is_subset ~of_:(Atom.tvs_of atm)
                              (ClauseOld.tvs_of
                                 ( senv,
                                   Set.remove pos atm,
                                   neg,
                                   Formula.mk_true () (*phi*) )),
                         n )
                   | None -> (
                       match
                         Set.find neg ~f:(Atom.pvs_of >> Fn.flip Set.mem pvar)
                       with
                       | Some atm ->
                           ( p,
                             n
                             && Set.is_subset ~of_:(Atom.tvs_of atm)
                                  (ClauseOld.tvs_of
                                     ( senv,
                                       pos,
                                       Set.remove neg atm,
                                       Formula.mk_true () (*phi*) )) )
                       | None -> (p, n))
                 else (p, n))
             |> uncurry ( || ))
    in
    let safe = Fn.non Set.is_empty pvs_info1 in
    (if safe then pvs_info1 else pvs_info2)
    |> Set.to_list
    |> List.sort
         ~compare:(fun
             (_, arity1, (pc1, nc1, pn1)) (_, arity2, (pc2, nc2, pn2)) ->
           if pc1 = 1 || nc1 = 1 then
             if pc2 = 1 || nc2 = 1 then
               if pn1 = pn2 then arity2 - arity1 else pn1 - pn2
             else -1
           else if pc2 = 1 || nc2 = 1 then 1
           else if pn1 = pn2 then arity2 - arity1
           else pn1 - pn2)
    |> function
    | [] -> clauses
    | (pv, arity, (pc, nc, _pn)) :: _rs ->
        Debug.print
        @@ lazy
             (sprintf
                "%s %s (arity %d) occurs %s times positively and %s times \
                 negatively"
                (if safe then "[safe]" else "[unsafe]")
                (Ident.name_of_pvar pv) arity (string_of_int pc)
                (string_of_int nc));
        (*List.iter rs ~f:(fun (pv, arity, (pc, nc, _pn)) ->
            Debug.print @@ lazy
              (sprintf "%s %s (arity %d) occurs %s times positively and %s times negatively"
                 (if safe then "[safe]" else "[unsafe]")
                 (Ident.name_of_pvar pv) arity (string_of_int pc) (string_of_int nc)));*)
        elim_pvars_by_resolution qelim exi_senv (Set.remove eliminable_pvs pv)
        @@ resolve qelim exi_senv pv clauses

  let elim_pvs ?(bpvs = Set.Poly.empty) pcsp =
    eliminated_pvars := Map.Poly.empty;
    let rec inner iter pcsp0 =
      let exi_senv = PCSP.Problem.senv_of pcsp0 in
      let eliminable_pvs =
        PCSP.Problem.pvs_of pcsp0
        |> Set.filter ~f:(fun t ->
               PCSP.Problem.is_ord_pred pcsp0 t && not (Set.mem bpvs t))
        |> Set.Poly.map ~f:Ident.tvar_to_pvar
      in
      let qelim = Qelim.qelim_old Map.Poly.empty exi_senv in
      let pcsp1 =
        PCSP.Problem.remove_unused_params
        @@ PCSP.Problem.elim_unsat_wf_predicates (*ToDo*) ~print:Debug.print
        @@
        if PCSP.Problem.is_cnf pcsp0 then pcsp0
        else
          PCSP.Problem.map_if_raw_old pcsp0 ~f:(fun inp ->
              (* note that phis may contain variables with the same name but different types *)
              let senvs, phis =
                Set.unzip
                @@
                if iter = 0 then Set.Poly.map ~f:Formula.refresh_tvar inp
                else inp
              in
              let senvs', phis =
                Set.unzip
                @@ Set.Poly.map ~f:(Formula.rm_quant ~forall:true) phis
              in
              let senv =
                Map.of_set_exn @@ Logic.of_old_sort_env_set @@ Set.concat
                @@ Set.union (Set.Poly.map ~f:Set.of_map senvs) senvs'
              in
              Debug.print
              @@ lazy
                   (sprintf "[elim_pvs] senv: %s"
                   @@ Logic.str_of_sort_env_list Logic.ExtTerm.str_of_sort
                   @@ Map.Poly.to_alist senv);
              Debug.print
              @@ lazy
                   (sprintf "[elim_pvs] bpvs: %s"
                   @@ String.concat_set ~sep:","
                   @@ Set.Poly.map bpvs ~f:Ident.name_of_tvar);
              Set.concat_map phis
                ~f:
                  (Formula.cnf_of (*ToDo*) Logic.(to_old_sort_env_map exi_senv))
              |> Set.Poly.map ~f:(fun (ps, ns, phi) ->
                     ClauseOld.reduce_sort_map (senv, ps, ns, phi))
              |> (fun cls ->
                   Debug.print @@ lazy "[elim_pvs] cls:";
                   Set.iter cls ~f:(fun c ->
                       Debug.print @@ lazy ("  " ^ ClauseOld.str_of c));
                   cls)
              (* begin: predicate variable elimination *)
              |> elim_one_side_unbounded_pvars exi_senv eliminable_pvs
              (* |> (fun cls -> Debug.print @@ lazy ("[elim_pvs]after elim_one_side_unbounded_pvars:"); Set.iter cls ~f:(fun c -> Debug.print @@ lazy ("  " ^ ClauseOld.str_of c)); cls) *)
              |> elim_pvars_with_lb_ub exi_senv eliminable_pvs
              (* |> (fun cls -> Debug.print @@ lazy ("[elim_pvs]after elim_pvars_with_lb_ub:"); Set.iter cls ~f:(fun c -> Debug.print @@ lazy ("  " ^ ClauseOld.str_of c)); cls) *)
              |> elim_pvars_by_resolution qelim exi_senv eliminable_pvs
              (* |> (fun cls -> Debug.print @@ lazy ("[elim_pvs]after elim_pvars_by_resolution:"); Set.iter cls ~f:(fun c -> Debug.print @@ lazy ("  " ^ ClauseOld.str_of c)); cls) *)
              (* end: predicate variable elimination *)
              |> Set.Poly.filter_map ~f:(fun cl ->
                     let open Option in
                     ClauseOld.simplify (Map.key_set exi_senv)
                       (Z3Smt.Z3interface.is_valid ~id:!id
                          (LogicOld.get_fenv ()))
                       cl
                     >>= fun cl ->
                     let senv, phi =
                       ClauseOld.to_formula @@ ClauseOld.reduce_sort_map cl
                     in
                     Some (Logic.to_old_sort_env_map senv, phi)))
      in
      if
        Map.Poly.equal Stdlib.( = )
          (PCSP.Problem.senv_of pcsp0)
          (PCSP.Problem.senv_of pcsp1)
      then pcsp1
      else (
        Debug.print @@ lazy "*** pcsp senv has been changed, repeat elim_pvs";
        inner (iter + 1) pcsp1)
    in
    let res = inner 0 pcsp in
    (!eliminated_pvars, res)
  (*ToDo: reconstruct solution for pvars eliminated by elim_pvars_by_resolution using solve_non_rec*)

  let solution_of_unit_clause clause =
    let _senv, ps, ns, phi = clause in
    let ftv = Formula.term_sort_env_of phi |> Set.elements in
    let quantifiers = fst @@ refresh_sort_env_list ftv in
    let subst_map =
      List.zip_exn ftv quantifiers
      |> List.map ~f:(fun ((tvar, sort), (bvar, sort')) ->
             assert (Stdlib.(sort = sort'));
             (tvar, Term.mk_var bvar sort))
      |> Map.Poly.of_alist_exn
    in
    let phi = Formula.subst subst_map phi in
    if Set.is_singleton ps then
      match Set.choose ps with
      | Some (Atom.App (Predicate.Var (pvar, sorts), terms, _)) ->
          let params = sort_env_list_of_sorts sorts in
          let phi =
            try
              Formula.exists quantifiers
              @@ List.fold
                   ~init:(Evaluator.simplify @@ Formula.mk_neg phi)
                   ~f:(fun phi ((tvar, sort), term) ->
                     let term = Term.subst subst_map term in
                     Formula.mk_and
                       (Formula.eq term (Term.mk_var tvar sort))
                       phi)
              @@ List.zip_exn params terms
            with _ -> failwith "params must be exactly same length to terms"
          in
          (pvar, (params, phi))
      | _ -> assert false
    else if Set.is_singleton ns then
      match Set.choose ns with
      | Some (Atom.App (Predicate.Var (pvar, sorts), terms, _)) ->
          let params = sort_env_list_of_sorts sorts in
          let phi =
            let condition =
              try
                List.fold ~init:None ~f:(fun c ((tvar, sort), term) ->
                    let eq =
                      Formula.eq
                        (Term.subst subst_map term)
                        (Term.mk_var tvar sort)
                    in
                    match c with
                    | None -> Some eq
                    | Some phi -> Some (Formula.mk_and eq phi))
                @@ List.zip_exn params terms
              with _ -> failwith "params must be exactly same length to terms"
            in
            match condition with
            | Some condition ->
                Formula.forall quantifiers @@ Formula.mk_imply condition phi
            | None -> failwith "there must be at least one params"
          in
          (pvar, (params, phi))
      | _ -> assert false
    else failwith "one of ps or ns has one element, the other does zero"

  let rec solve_non_rec unknowns cnf =
    let pvar, (senv, phi) =
      match
        Set.find cnf ~f:(fun (_, ps, ns, _) ->
            Set.length ps + Set.length ns = 1)
      with
      | Some clause -> solution_of_unit_clause clause
      | None ->
          failwith
            "At least one clause must have exactly one predicate variable."
    in
    let psub = Map.Poly.singleton pvar (senv, phi, Formula.mk_neg phi, false) in
    let cnf1, cnf2 = subst_preds unknowns psub cnf in
    let cnf = Set.union cnf1 cnf2 in
    (pvar, (senv, phi))
    :: (if Set.is_empty cnf then [] else solve_non_rec unknowns cnf)
end
