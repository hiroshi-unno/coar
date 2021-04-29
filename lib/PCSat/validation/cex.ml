open Core
open Common.Util
open PCSatCommon
open Ast

let check_clause_nonparam ?(smt_timeout=None) fenv phi =
  Z3Smt.Z3interface.check_sat ~timeout:smt_timeout fenv [ LogicOld.Formula.mk_neg phi ]

let check_clause_param_smt ?(smt_timeout=None) fenv params_senv uni_senv phi =
  let usenv = Logic.SortMap.to_old_sort_env Logic.ExtTerm.to_old_sort uni_senv in
  match Z3Smt.Z3interface.check_sat ~timeout:smt_timeout fenv [LogicOld.Formula.forall usenv phi] with
  | `Sat _model -> `Unsat(*ToDo: show model for parameters of the candidate solution *)
  | _ -> (* unsat, unknown, timeout*)
    let sub = Logic.SortMap.to_old_dummies Logic.ExtTerm.to_old_sort params_senv in
    check_clause_nonparam fenv (LogicOld.Formula.subst sub phi)

let check_clause_param_strat_synth ?(smt_timeout=None) fenv params_senv uni_senv phi =
  let open QSMT.StrategySynthesis in
  let open LIAStrategySynthesis in
  let esenv = LogicOld.SortEnv.of_list @@ List.map ~f:(fun (x, s) -> x, Logic.ExtTerm.to_old_sort s) @@ Logic.SortMap.to_alist params_senv in
  let usenv = LogicOld.SortEnv.of_list @@ List.map ~f:(fun (x, s) -> x, Logic.ExtTerm.to_old_sort s) @@ Logic.SortMap.to_alist uni_senv in
  let f = Evaluator.simplify @@ LogicOld.Formula.elim_ite @@
    LogicOld.Formula.exists esenv @@
    LogicOld.Formula.forall usenv @@
    LogicOld.Formula.aconv_tvar phi(*ToDo: this is necessary due to a bug?*) in
  (*print_endline @@ (Printf.sprintf "original input: %s\n" (LogicOld.Formula.str_of f));*)
  match LIA.formula_of_term @@ Logic.ExtTerm.of_old_formula f with
  | None -> (* f is possibly non-linear *)
    check_clause_param_smt ~smt_timeout fenv params_senv uni_senv phi
  | Some f ->
    (*Debug.print @@ lazy (Printf.sprintf "input: %s\n" (formula_to_string f));*)
    let p, s = nondet_strategy_synthesis f in
    (*Debug.print @@ lazy (Printf.sprintf "strategy skelton for %s:\n%s" (player_to_string p) (ssforest_to_string s));*)
    match p with
    | SAT -> `Unsat(*ToDo: show model for parameters of the candidate solution*)
    | UNSAT ->
      let f = PreFormula.neg_formula LIA.neg_atom f in
      let fml, chc, det, params = loseCHC [] s f in
      (*Debug.print @@ lazy "strategy template:";
        Map.Poly.iteri det ~f:(fun ~key ~data:(senv, t) ->
        Debug.print @@ lazy
        (Printf.sprintf "%s: %s" (Ident.name_of_tvar key)
          (LogicOld.Term.str_of @@ ExtTerm.to_old_term
             (SortMap.merge (Map.Poly.of_alist_exn params) senv) t [])));
        Debug.print @@ lazy "";*)
      let chc = (Logic.SortMap.empty, Logic.Term.mk_apps (Logic.BoolTerm.mk_imply ()) [fml; Logic.BoolTerm.mk_bool false]) :: chc in
      let problem = PCSP.Problem.of_formulas ~params:(PCSP.Params.make @@ Logic.SortMap.of_set @@ Set.Poly.of_list params) (Set.Poly.of_list chc) in
      (*Debug.print @@ lazy "recursion-free CHC problem for determinization:";
        Debug.print @@ lazy (PCSP.Problem.str_of problem);
        Debug.print @@ lazy "";*)
      (match PCSP.ForwardPropagate.solve problem with
       | Ok (PCSP.Problem.Sat subs) ->
         (*Debug.print @@ lazy ("solution:\n" ^ Logic.Term.str_of_subst ExtTerm.str_of subs);*)
         let ds = Map.Poly.map ~f:(fun (senv, t) -> senv, Logic.ExtTerm.subst subs t) det in
         (*print_endline @@ (Printf.sprintf "determinized strategy for %s:" (player_to_string p));
           Map.Poly.iteri ds ~f:(fun ~key ~data:(senv, t) ->
             print_endline @@ (Printf.sprintf "%s: %s" (Ident.name_of_tvar key) (LogicOld.Term.str_of @@ LogicOld.Term.simplify @@ Logic.ExtTerm.to_old_term senv t [])));*)
         `Sat (Map.Poly.to_alist ds
               |> List.map ~f:(fun (x, (senv, t)) ->
                   let t = fix ~f:(Logic.Term.subst (Map.Poly.map ds ~f:(fun (_, t) -> t))) ~equal:Stdlib.(=) t in
                   (x, LogicOld.T_bool.SBool), Some (Logic.ExtTerm.to_old_term senv t [])))
       | Ok PCSP.Problem.Unsat -> assert false
       | Ok PCSP.Problem.Unknown -> assert false
       | Error err -> failwith (Error.to_string_hum err))

(* [pcs] indicates whether parametric candidate solutions are enabled
   [pex] indicates whether parametric examples are enabled *)
let of_cand ?(smt_timeout=None) pcs pex ss pcsp fenv ((params_senv, cand) : CandSol.t) =
  let cand_map = CandSol.to_subst (params_senv, cand) in
  let cls_nonparam, cls_param =
    Set.Poly.map (PCSP.Problem.clauses_of pcsp) ~f:(fun cl ->
        let uni_senv = Clause.sort_env_of cl in
        let clause = Clause.to_formula cl in
        let phi =
          Evaluator.simplify @@
          Logic.ExtTerm.to_old_formula
            (Logic.SortMap.merge params_senv uni_senv) (Logic.Term.subst cand_map clause) [] in
        let fvs = LogicOld.Formula.tvs_of phi in
        let uni_senv' = Logic.SortMap.filter_keys uni_senv ~f:(Set.Poly.mem fvs) in
        let params_senv' = Logic.SortMap.filter_keys params_senv ~f:(Set.Poly.mem fvs) in
        uni_senv, clause, params_senv', uni_senv', phi)
    |> Set.Poly.partition_tf ~f:(fun (_, _, params_senv, _, _) -> Logic.SortMap.is_empty params_senv)
  in
  let cls_nonparam = Set.Poly.map cls_nonparam ~f:(fun (uni_senv, clause, _, _, phi) ->
      (* non-parametric candidate solution *)
      [uni_senv, clause], phi, check_clause_nonparam ~smt_timeout fenv phi) in
  let cls_param =
    Set.Poly.of_list @@
    List.map ~f:(fun (cls, params_senv', uni_senv', phi) ->
        (* parametric candidate solution *)
        assert (pcs && pex);
        cls, phi,
        if ss then (* apply strategy synthesis to forall-exists formula *)
          check_clause_param_strat_synth ~smt_timeout fenv params_senv' uni_senv' phi
        else (* apply SMT solving to forall-exists formula *)
          check_clause_param_smt ~smt_timeout fenv params_senv' uni_senv' phi) @@
    List.map ~f:(List.fold
                   ~init:([], Map.Poly.empty, Map.Poly.empty, LogicOld.Formula.mk_true ())
                   ~f:(fun (cls, params_senv, uni_senv, phi) (uni_senv0, clause0, params_senv', uni_senv', phi') ->
                       (uni_senv0, clause0) :: cls,
                       Map.force_merge params_senv params_senv',
                       Map.force_merge uni_senv uni_senv',
                       LogicOld.Formula.mk_and phi phi')) @@
    List.classify (fun (_, _, senv1, _, _) (_, _, senv2, _, _) ->
        not @@ Set.Poly.is_empty @@ Set.Poly.inter (Set.Poly.of_list @@ Map.Poly.keys senv1) (Set.Poly.of_list @@ Map.Poly.keys senv2)) @@
    Set.Poly.to_list cls_param
  in
  Set.concat_map (Set.Poly.union cls_nonparam cls_param) ~f:(fun (cls, phi, res) ->
      match res with
      | `Sat model -> (* not all but some clause in cls caused a countermodel *)
        let res =
          Set.Poly.union_list @@
          List.map cls ~f:(fun (uni_senv, clause) ->
              let phi_clause = 
                Logic.ExtTerm.to_old_formula
                  (Logic.SortMap.merge (PCSP.Problem.senv_of pcsp) uni_senv) clause []
              in
              ExClauseSet.of_model (PCSP.Problem.senv_of pcsp) pex (uni_senv, phi_clause) model)
        in
        if not @@ Set.Poly.is_empty res then (* note that res never represents true *)
          res
        else
          let ctx = Z3.mk_context [("MODEL", "true")] in
          let dtenv = Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx (PCSP.Problem.dtenv_of pcsp) in
          failwith ("model: " ^ LogicOld.TermSubst.str_of_model model ^
                    "\ncandidate: " ^ CandSol.str_of (params_senv, cand) ^
                    "\nphi: " ^ LogicOld.Formula.str_of phi ^
                    "\nz3 input: " ^ Z3.Expr.to_string @@ Z3Smt.Z3interface.of_formula ctx Env.empty Env.empty fenv dtenv@@ LogicOld.Formula.mk_neg phi)
      | `Unsat -> Set.Poly.empty
      | _ -> 
        (*failwith "Z3 reported unknown or timeout in the validation phase"*)
        Set.Poly.singleton @@ ExClause.mk_unit_pos @@ ExAtom.mk_true () (*dummy*))

let common_cex_of_clause fenv num_ex exi_senv candidates clause =
  let uni_senv = Clause.sort_env_of clause in
  let clause = Clause.to_formula clause in
  let spurious_cands =
    Set.Poly.of_list @@ List.filter candidates ~f:(fun cand ->
        let cand_map = CandSol.to_subst cand in
        not @@ Z3Smt.Z3interface.is_valid fenv @@
        Logic.ExtTerm.to_old_formula uni_senv (Logic.Term.subst cand_map clause) [])
  in
  let phis =
    List.map (Set.Poly.to_list spurious_cands) ~f:(fun cand ->
        let cand_map = CandSol.to_subst cand in
        LogicOld.Formula.mk_neg @@
        Logic.ExtTerm.to_old_formula uni_senv (Logic.Term.subst cand_map clause) [])
  in
  Z3Smt.Z3interface.max_smt_of fenv num_ex phis
  |> Set.concat_map ~f:(fun model ->
      let senv = Logic.SortMap.merge exi_senv uni_senv in 
      let examples =
        ExClauseSet.of_model exi_senv false
          (senv, Logic.ExtTerm.to_old_formula senv clause [])
          model
      in
      assert (not @@ Set.Poly.is_empty examples);
      examples),
  spurious_cands
