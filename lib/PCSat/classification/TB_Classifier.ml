open Core
open Common
open Common.Ext
open Common.Util
open Ast
open Ast.LogicOld
open PCSatCommon
open PCSatCommon.HypSpace
open Template.Function

module Config = struct
  type kind =
    | Ord_DNF of Template.PredicateDNF.Config.t ext_file
    | Ord_Flex of Template.PredicateFlex.Config.t ext_file
    | WF of Template.WFPredicate.Config.t ext_file
    | WF_Flex of Template.WFPredicateFlex.Config.t ext_file
    | FN of Template.FNPredicate.Config.t ext_file
    | FN_Flex of Template.FNPredicateFlex.Config.t ext_file
  [@@deriving yojson]

  type t = { verbose : bool; kind : kind } [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let instantiate_ext_files cfg =
    let open Or_error in
    match cfg.kind with
    | Ord_DNF cfg_ord ->
        Template.PredicateDNF.Config.load_ext_file cfg_ord >>= fun cfg_ord ->
        Ok { cfg with kind = Ord_DNF cfg_ord }
    | Ord_Flex cfg_ord ->
        Template.PredicateFlex.Config.load_ext_file cfg_ord >>= fun cfg_ord ->
        Ok { cfg with kind = Ord_Flex cfg_ord }
    | WF cfg_wf ->
        Template.WFPredicate.Config.load_ext_file cfg_wf >>= fun cfg_wf ->
        Ok { cfg with kind = WF cfg_wf }
    | WF_Flex cfg_wf ->
        Template.WFPredicateFlex.Config.load_ext_file cfg_wf >>= fun cfg_wf ->
        Ok { cfg with kind = WF_Flex cfg_wf }
    | FN cfg_fn ->
        Template.FNPredicate.Config.load_ext_file cfg_fn >>= fun cfg_fn ->
        Ok { cfg with kind = FN cfg_fn }
    | FN_Flex cfg_fn ->
        Template.FNPredicateFlex.Config.load_ext_file cfg_fn >>= fun cfg_fn ->
        Ok { cfg with kind = FN_Flex cfg_fn }
end

module Make (Cfg : Config.ConfigType) (APCSP : PCSP.Problem.ProblemType) =
struct
  let config = Cfg.config
  let id = PCSP.Problem.id_of APCSP.problem

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id

  type classifier = sort_env_map * (Ident.pvar * (sort_env_list * Formula.t))

  let fenv = Map.Poly.empty (*TODO : generate fenv*)
  let qdeps = Map.Poly.empty (* TODO:generate qdeps*)

  let get_key =
    let key_cnt = ref 0 in
    fun () ->
      incr key_cnt;
      sprintf "#S_%d" !key_cnt

  let mk_classifier pvar (params : sort_env_list) table labeling _examples =
    let (module FT) =
      let module M = struct
        let name : Ident.tvar = Ident.pvar_to_tvar pvar
        let sorts : Sort.t list = List.map ~f:snd params

        (*let dtenv : LogicOld.DTEnv.t = Map.Poly.empty*)
        let fenv : LogicOld.FunEnv.t = Map.Poly.empty
        let sol_space = PCSP.Problem.sol_space_of APCSP.problem
        let id = id
      end in
      match config.kind with
      | Ord_DNF cfg ->
          (module Template.PredicateDNF.Make
                    (struct
                      let config = ExtFile.unwrap_or_abort cfg
                    end)
                    (M) : Template.Function.Type)
      | Ord_Flex cfg ->
          (module Template.PredicateFlex.Make
                    (struct
                      let config = ExtFile.unwrap_or_abort cfg
                    end)
                    (M) : Template.Function.Type)
      | WF cfg ->
          (module Template.WFPredicate.Make
                    (struct
                      let config = ExtFile.unwrap_or_abort cfg
                    end)
                    (M) : Template.Function.Type)
      | WF_Flex cfg ->
          (module Template.WFPredicateFlex.Make
                    (struct
                      let config = ExtFile.unwrap_or_abort cfg
                    end)
                    (M) : Template.Function.Type)
      | FN cfg ->
          (module Template.FNPredicate.Make
                    (struct
                      let config = ExtFile.unwrap_or_abort cfg
                    end)
                    (M) : Template.Function.Type)
      | FN_Flex cfg ->
          (module Template.FNPredicateFlex.Make
                    (struct
                      let config = ExtFile.unwrap_or_abort cfg
                    end)
                    (M) : Template.Function.Type)
    in
    let alist = labeling in
    let tt = TruthTable.get_table table pvar in
    Debug.print
    @@ lazy (sprintf "    labeled atoms (%d):" (TruthTable.num_atoms alist));
    Debug.print @@ lazy (TruthTable.str_of_atoms tt alist);
    let pos_neg_ex =
      let neg_ex, pneg_ex, pos_ex, ppos_ex = TruthTable.papps_of tt alist in
      assert (Set.is_empty pneg_ex && Set.is_empty ppos_ex);
      Set.union
        (Set.Poly.map ~f:(fun a -> (true, a)) pos_ex)
        (Set.Poly.map ~f:(fun a -> (false, a)) neg_ex)
    in
    (*let quals = TruthTable.qualifiers tt in*)
    let rec inner () =
      let tag = None in
      let ( (update_label, template),
            temp_param_cnstrs,
            temp_param_senv,
            qualifiers ) =
        FT.gen_template ~tag ~ucore:false
        @@ {
             depth = -1;
             params = FT.params_of ~tag;
             quals = Set.Poly.empty (*quals*);
             qdeps = Map.Poly.empty;
             terms = Set.Poly.empty;
             consts = Set.Poly.empty;
           }
      in
      let hole_qualifiers_map =
        List.map qualifiers ~f:(fun (tvar, quals) ->
            ( tvar,
              List.map quals ~f:(fun (tvar, (env, phi)) ->
                  ( tvar,
                    (TruthTable.index_of_qual ~id tt fenv qdeps phi, env, phi)
                  )) ))
      in
      Debug.print @@ lazy "templates generated";
      let key_constr_map, key_tvar_update_list_map =
        Set.fold ~init:(Map.Poly.empty, Map.Poly.empty) pos_neg_ex
          ~f:(fun
              (key_constr_map, key_tvar_update_list_map)
              (polarity, ((pvar, sorts), args))
            ->
            let atom = ExAtom.mk_papp pvar sorts args in
            let key = get_key () in
            let eval_qual (key, (qi, _params, _phi)) =
              let ai =
                TruthTable.index_of_atom ~id tt fenv qdeps
                  (ExAtom.normalize_params atom)
              in
              let e = tt.table.{qi, ai} in
              if e = 1 then
                Logic.ExtTerm.geq_of (Logic.Term.mk_var key)
                  (Logic.ExtTerm.zero ())
              else if e = -1 then
                Logic.ExtTerm.leq_of (Logic.Term.mk_var key)
                  (Logic.ExtTerm.zero ())
              else if
                (*Debug.print @@ lazy (ExAtom.str_of atom ^ " on " ^ Formula.str_of phi ^ " couldn't be evaluated.  This may cause a violation of the progress property.");*)
                not polarity
              then Logic.ExtTerm.mk_bool true
              else
                Logic.ExtTerm.eq_of Logic.ExtTerm.SInt (Logic.Term.mk_var key)
                  (Logic.ExtTerm.zero ())
            in
            let hole_map =
              List.map hole_qualifiers_map ~f:(fun (hole, quals) ->
                  ( hole,
                    if List.is_empty quals then
                      Logic.Term.mk_lambda
                        (Logic.of_old_sort_env_list
                        @@ sort_env_list_of_sorts sorts)
                      @@ Logic.BoolTerm.mk_bool true
                    else
                      let _, (_, qsenv, _) = List.hd_exn quals in
                      Logic.Term.mk_lambda (Logic.of_old_sort_env_list qsenv)
                      @@ Logic.BoolTerm.and_of
                      @@ List.map quals ~f:eval_qual ))
              |> Map.Poly.of_alist_exn
            in
            let constr =
              ExAtom.to_formula true atom
              |> snd
              |> Logic.Term.subst
                   (Map.Poly.singleton (Ident.pvar_to_tvar pvar) template)
              |> Logic.Term.subst hole_map
              |> (fun phi ->
                   Logic.ExtTerm.to_old_fml Map.Poly.empty (temp_param_senv, phi))
              |> if polarity then Evaluator.simplify else Evaluator.simplify_neg
            in
            ( Map.Poly.add_exn key_constr_map ~key ~data:constr,
              Map.Poly.add_exn key_tvar_update_list_map ~key ~data:update_label
            ))
      in
      let key_constr_map, key_tvar_update_list_map =
        let used_param_senv =
          Set.of_map key_constr_map
          |> Set.concat_map ~f:(fun (_, phi) -> Formula.tvs_of phi)
          |> Set.concat_map ~f:(fun (Ident.Tvar x) ->
                 Set.Poly.of_list
                   [
                     Ident.Tvar x;
                     Ident.Tvar (x ^ "#pos" (*ToDo*));
                     Ident.Tvar (x ^ "#neg" (*ToDo*));
                   ])
        in
        List.fold temp_param_cnstrs
          ~init:(key_constr_map, key_tvar_update_list_map)
          ~f:(fun
              (key_constr_map, key_tvar_update_list_map)
              (update_label, cnstr)
            ->
            let key = get_key () in
            let param_constr =
              let dis_map =
                Map.Poly.filter_mapi temp_param_senv ~f:(fun ~key ~data ->
                    assert (Ident.is_parameter key);
                    if Set.mem used_param_senv key then None
                    else Some (Logic.mk_old_dummy data))
              in
              Logic.ExtTerm.to_old_fml Map.Poly.empty (temp_param_senv, cnstr)
              |> Formula.subst dis_map |> Evaluator.simplify
            in
            ( Map.Poly.add_exn key_constr_map ~key ~data:param_constr,
              Map.Poly.add_exn key_tvar_update_list_map ~key ~data:update_label
            ))
      in
      Debug.print @@ lazy "constraints generated";
      match
        Z3Smt.Z3interface.check_sat_unsat_core ~id Map.Poly.empty key_constr_map
      with
      | `Sat model ->
          Debug.print @@ lazy "sat";
          let model =
            List.map model ~f:(fun ((x, s), t_opt) ->
                ( (x, Logic.ExtTerm.of_old_sort s),
                  Option.(
                    t_opt >>= fun t -> return (Logic.ExtTerm.of_old_term t)) ))
          in
          let temp_param_sub =
            Map.Poly.mapi temp_param_senv ~f:(fun ~key ~data ->
                (match
                   List.find model ~f:(fun ((x, _), _) -> Stdlib.(x = key))
                 with
                | None -> ((key, data), None)
                | Some opt -> opt)
                |> Logic.ExtTerm.remove_dontcare_elem
                   (* ToDo: support parameteric candidate solution and CEGIS(T)*)
                |> snd)
          in
          let hole_sub =
            Map.Poly.of_alist_exn
            @@ List.map hole_qualifiers_map ~f:(fun (hole, quals) ->
                   ( hole,
                     if List.is_empty quals then
                       Logic.Term.mk_lambda (Logic.of_old_sort_env_list params)
                       @@ Logic.BoolTerm.mk_bool true
                     else
                       let senv =
                         let _, (_, qsenv, _) = List.hd_exn quals in
                         Logic.of_old_sort_env_list qsenv
                       in
                       Template.Generator.gen_from_qualifiers (senv, quals) ))
          in
          let phi =
            Logic.ExtTerm.subst temp_param_sub
            @@ Logic.ExtTerm.subst hole_sub template
          in
          assert (Set.is_empty @@ Logic.ExtTerm.fvs_of phi);
          let phi =
            Logic.ExtTerm.to_old_formula Map.Poly.empty
              (Map.Poly.of_alist_exn @@ Logic.of_old_sort_env_list params)
              phi
              (List.map ~f:Logic.ExtTerm.of_old_term @@ Term.of_sort_env params)
          in
          Ok
            [
              ( Map.Poly.empty (* parameters of parametric candidate*),
                (pvar, (params, phi)) );
            ]
      | `Unsat unsat_keys ->
          Debug.print
          @@ lazy ("unsat, reason:" ^ String.concat unsat_keys ~sep:",");
          let unsat_keys =
            List.map unsat_keys ~f:(fun str ->
                String.sub str ~pos:1 ~len:(String.length str - 2))
          in
          let labels =
            List.fold unsat_keys ~init:Set.Poly.empty ~f:(fun labels key ->
                Set.add labels @@ Map.Poly.find_exn key_tvar_update_list_map key)
          in
          FT.update_with_labels labels;
          inner ()
      | `Unknown reason ->
          Debug.print @@ lazy ("unknown:" ^ reason);
          FT.update_with_labels (Set.Poly.singleton TimeOut);
          inner ()
      | `Timeout ->
          Debug.print @@ lazy "timeout";
          FT.update_with_labels (Set.Poly.singleton TimeOut);
          inner ()
    in
    inner ()
end
