(** Validator *)

open Core
open Common
open Common.Combinator
open Common.Ext
open Common.Util
open PCSatCommon
open Ast

module type ValidatorType = sig
  val run_phase : int -> State.s -> State.u Or_error.t
end

(** configuration of validator *)
module Config = struct
  type cex_strategy = AllExamples | ExamplesUpTo of int [@@deriving yojson]
  type t = {
    verbose: bool;
    parametric_candidates: bool; (* whether parametric candidate solutions are enabled *)
    parametric_examples: bool; (* whether parametric examples are enabled *)
    strategy_synthesis: bool; (* require that parametric_examples = true*)
    smt_timeout: int option;
    cex_strategy: cex_strategy;
    check_part_sol_with_lbs: bool
  } [@@deriving yojson]

  module type ConfigType = sig val config : t end

  let instantiate_ext_files cfg = Ok cfg

  let load_ext_file = function
    | ExtFile.Filename filename ->
      begin
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename)
        >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x ->
          instantiate_ext_files x >>= fun x ->
          Ok (ExtFile.Instance x)
        | Error msg ->
          error_string @@ Printf.sprintf
            "Invalid Validator Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (Instance x)
end

module Make (RLCfg: RLConfig.ConfigType) (Cfg: Config.ConfigType) (APCSP: PCSP.Problem.ProblemType)
  : ValidatorType = struct
  let config = Cfg.config
  let id = PCSP.Problem.id_of APCSP.problem

  module Debug = Debug.Make (val Debug.Config.(if config.verbose then enable else disable))
  let _ = Debug.set_id id

  open Debug

  let check_clause_nonparam_smt ?(timeout=None) fenv phi =
    let phi = Evaluator.simplify @@ LogicOld.Formula.mk_neg phi in
    Debug.print @@ lazy (sprintf "[check valid -> sat] %s" @@ LogicOld.Formula.str_of phi);
    Z3Smt.Z3interface.check_sat ~id ~timeout fenv [ phi ]

  let check_clause_param_smt ?(timeout=None) fenv params_senv uni_senv phi =
    let usenv = Map.Poly.to_alist @@ Logic.to_old_sort_env_map Logic.ExtTerm.to_old_sort uni_senv in
    match Z3Smt.Z3interface.check_sat ~id ~timeout fenv [LogicOld.Formula.forall usenv phi] with
    | `Sat _model -> `Unsat(*ToDo: show model for parameters of the candidate solution *)
    | _ -> (* unsat, unknown, timeout*)
      let sub = Logic.to_old_dummies Logic.ExtTerm.to_old_sort params_senv in
      check_clause_nonparam_smt fenv (LogicOld.Formula.subst sub phi)

  let check_clause_param_strat_synth ?(timeout=None) fenv params_senv uni_senv phi =
    let open QSMT.StrategySynthesis in
    let open LIAStrategySynthesis in
    let esenv = List.map ~f:(fun (x, s) -> x, Logic.ExtTerm.to_old_sort s) @@ Map.Poly.to_alist params_senv in
    let usenv = List.map ~f:(fun (x, s) -> x, Logic.ExtTerm.to_old_sort s) @@ Map.Poly.to_alist uni_senv in
    let f = Evaluator.simplify @@ LogicOld.Formula.elim_ite @@
      LogicOld.Formula.exists esenv @@ LogicOld.Formula.forall usenv @@
      LogicOld.Formula.aconv_tvar phi(*ToDo: this is necessary due to a bug?*) in
    (*print_endline @@ (Printf.sprintf "original input: %s\n" (LogicOld.Formula.str_of f));*)
    match LIA.formula_of_term @@ Logic.ExtTerm.of_old_formula f with
    | None -> (* f is possibly non-linear *)
      check_clause_param_smt ~timeout fenv params_senv uni_senv phi
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
            (Logic.ExtTerm.str_of_term
              (Map.force_merge (Map.Poly.of_alist_exn params) senv) t)));
          Debug.print @@ lazy "";*)
        let chc = (Map.Poly.empty, Logic.Term.mk_apps (Logic.BoolTerm.mk_imply ()) [fml; Logic.BoolTerm.mk_bool false]) :: chc in
        let problem = PCSP.Problem.of_formulas ~params:(PCSP.Params.make @@ Map.of_list_exn params) (Set.Poly.of_list chc) in
        (*Debug.print @@ lazy "recursion-free CHC problem for determinization:";
          Debug.print @@ lazy (PCSP.Problem.str_of problem);
          Debug.print @@ lazy "";*)
        (match PCSP.ForwardPropagate.solve problem with
         | Ok (PCSP.Problem.Sat subs) ->
           (*Debug.print @@ lazy ("solution:\n" ^ Logic.str_of_term_subst Logic.ExtTerm.str_of subs);*)
           let ds = Map.Poly.map ~f:(fun (senv, t) -> senv, Logic.ExtTerm.subst subs t) det in
           (*print_endline @@ (Printf.sprintf "determinized strategy for %s:"
                               (player_to_string p));
             Map.Poly.iteri ds ~f:(fun ~key ~data:(senv, t) ->
               print_endline @@
               (Printf.sprintf "%s: %s"
                  (Ident.name_of_tvar key)
                  (LogicOld.ExTerm.str_of_term params_senv(*ToDo*) senv t)));*)
           `Sat (List.map (Map.Poly.to_alist ds) ~f:(fun (x, (senv, t)) ->
               let t = fix ~f:(Logic.Term.subst (Map.Poly.map ds ~f:snd)) ~equal:Stdlib.(=) t in
               (x, LogicOld.T_bool.SBool),
               Some (Logic.ExtTerm.to_old_term Map.Poly.empty senv t [])))
         | Ok PCSP.Problem.Unsat -> assert false
         | Ok PCSP.Problem.Unknown -> assert false
         | Ok PCSP.Problem.OutSpace _ -> assert false
         | Error err -> failwith (Error.to_string_hum err))

  let find_all_counterexamples clauses fenv ((params_senv, cand) : CandSol.t) =
    let cand_map = CandSol.to_subst (params_senv, cand) in
    let cls_nonparam, cls_param =
      Set.Poly.partition_tf ~f:(fun ((_, _, params_senv, _, _), _) ->
          Map.Poly.is_empty params_senv) @@
      Set.Poly.map clauses ~f:(fun cl ->
          let uni_senv = Clause.sort_env_of cl in
          let clause = Clause.to_formula cl in
          let phi = Evaluator.simplify @@
            Logic.ExtTerm.to_old_formula Map.Poly.empty
              (Map.force_merge params_senv uni_senv)
              (Logic.Term.subst cand_map clause) [] in
          let fvs = LogicOld.Formula.tvs_of phi in
          let uni_senv' = Map.Poly.filter_keys uni_senv ~f:(Set.Poly.mem fvs) in
          let params_senv' = Map.Poly.filter_keys params_senv ~f:(Set.Poly.mem fvs) in
          (uni_senv, clause, params_senv', uni_senv', phi),
          (ClauseGraph.Clause cl, true))
    in
    let cls_nonparam =
      Set.Poly.map cls_nonparam ~f:(fun ((uni_senv, clause, _, _, phi), cl) ->
          (* non-parametric candidate solution *)
          ([uni_senv, clause], phi,
           check_clause_nonparam_smt ~timeout:config.smt_timeout fenv phi),
          [cl])
    in
    let cls_param =
      Set.Poly.to_list cls_param
      |> List.classify (fun ((_, _, senv1, _, _), _) ((_, _, senv2, _, _), _) ->
          Fn.non Set.Poly.is_empty @@ Set.Poly.inter
            (Set.Poly.of_list @@ Map.Poly.keys senv1)
            (Set.Poly.of_list @@ Map.Poly.keys senv2))
      |> List.map ~f:(fun rs ->
          let (cls, params_senv', uni_senv', phi), cl =
            List.fold rs
              ~init:(([], Map.Poly.empty, Map.Poly.empty, LogicOld.Formula.mk_true ()), [])
              ~f:(fun ((cls, params_senv, uni_senv, phi), srcs)
                   ((uni_senv0, clause0, params_senv', uni_senv', phi'), src_cl) ->
                   ((uni_senv0, clause0) :: cls,
                    Map.force_merge params_senv params_senv',
                    Map.force_merge uni_senv uni_senv',
                    LogicOld.Formula.mk_and phi phi'),
                   src_cl :: srcs)
          in
          (* parametric candidate solution *)
          assert config.parametric_candidates;
          (cls, phi,
           if config.strategy_synthesis then begin
             (* apply strategy synthesis to forall-exists formula *)
             assert config.parametric_examples;
             check_clause_param_strat_synth ~timeout:config.smt_timeout fenv params_senv' uni_senv' phi
           end else (* apply SMT solving to forall-exists formula *)
             check_clause_param_smt ~timeout:config.smt_timeout fenv params_senv' uni_senv' phi),
          cl)
      |> Set.Poly.of_list
    in
    Set.Poly.union cls_nonparam cls_param
    |> Set.concat_map ~f:(fun ((cls, phi, res), src_cl) ->
        match res with
        | `Sat model -> (* not all but some clause in cls has a countermodel *)
          let res =
            Set.Poly.union_list @@
            List.map cls ~f:(fun (uni_senv, clause) ->
                let phi_clause =
                  Logic.ExtTerm.to_old_formula
                    (PCSP.Problem.senv_of APCSP.problem) uni_senv clause []
                in
                ExClauseSet.of_model (PCSP.Problem.senv_of APCSP.problem) config.parametric_examples (uni_senv, phi_clause) model)
          in
          if Fn.non Set.Poly.is_empty res then
            Set.Poly.map res ~f:(fun ex -> ex, src_cl)
          else
            (* note that res never represents true *)
            let ctx = Z3.mk_context [("MODEL", "true")] in
            let dtenv =
              Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx (PCSP.Problem.dtenv_of APCSP.problem)
            in
            failwith ("model: " ^ LogicOld.str_of_model model ^
                      "\ncandidate: " ^ CandSol.str_of (params_senv, cand) ^
                      "\nphi: " ^ LogicOld.Formula.str_of phi ^
                      "\nz3 input: " ^ Z3.Expr.to_string @@ Z3Smt.Z3interface.of_formula ctx [] [] fenv dtenv @@ LogicOld.Formula.mk_neg phi)
        | `Unsat -> Set.Poly.empty
        | _ ->
          (*failwith "Z3 reported unknown or timeout in the validation phase"*)
          Set.Poly.singleton @@ (ExClause.mk_unit_pos @@ ExAtom.mk_true (), [ClauseGraph.Dummy, true]) (*dummy*))

  (** ToDo: fix to use real MaxSMT *)
  let find_common_counterexamples_for_clause fenv num_ex (candidates : (Ast.CandSol.t * CandSol.tag) list) clause =
    let exi_senv = PCSP.Problem.senv_of APCSP.problem in
    let uni_senv = Clause.sort_env_of clause in
    let clause = Clause.to_formula clause in
    let cand_phi_list =
      List.map candidates ~f:(fun (cand, cand_tag) ->
          let cand_map = CandSol.to_subst cand in
          cand,
          (cand_tag,
           LogicOld.Formula.mk_neg @@
           Logic.ExtTerm.to_old_formula uni_senv Map.Poly.empty
             (Logic.Term.subst cand_map clause) []))
    in
    let spurious_cand_phi_list =
      List.filter cand_phi_list ~f:(fun (_, (_, phi)) -> Z3Smt.Z3interface.is_sat ~id fenv phi)
    in
    List.filter_map spurious_cand_phi_list ~f:(function
        | (_, (CandSol.Total true, phi)) -> Some phi
        | _ -> None)
    |> Z3Smt.Z3interface.max_smt_of ~id fenv num_ex
    |> Set.concat_map ~f:(fun model ->
        let examples =
          ExClauseSet.of_model exi_senv false
            (Map.force_merge exi_senv uni_senv,
             Logic.ExtTerm.to_old_formula exi_senv uni_senv clause [])
            model
        in
        assert (Fn.non Set.Poly.is_empty examples);
        examples),
    Set.Poly.of_list @@ List.map ~f:fst spurious_cand_phi_list

  let validate vs (candidates : (Ast.CandSol.t * CandSol.tag) list) =
    let fenv = VersionSpace.fenv_of vs in
    let senv = PCSP.Problem.senv_of APCSP.problem in
    let messenger = PCSP.Problem.messenger_of APCSP.problem in
    print @@ lazy "**** Validator";
    print @@ lazy
      (String.concat_mapi_list ~sep:"\n" candidates ~f:(fun i (candidate, cand_tag) ->
           Printf.sprintf "**** %s candidate solution[%s] %s\n%s\n"
             (Ordinal.string_of @@ Ordinal.make i)
             (match cand_tag with
              | CandSol.Partial (Ident.Tvar key) ->
                (if config.check_part_sol_with_lbs then "LB_" else "") ^ key
              | Total _ -> if config.check_part_sol_with_lbs then "LB" else "-")
             (match cand_tag with CandSol.Total true -> "" | _ -> "without sampling")
             (CandSol.str_of candidate)));
    Messenger.receive_bounds messenger id APCSP.problem vs;
    let learned_clauses = VersionSpace.learned_clauses_of vs in
    print @@ lazy (VersionSpace.str_of_learned_clauses senv @@ learned_clauses);
    let clauses =
      Set.Poly.union (PCSP.Problem.clauses_of APCSP.problem) @@
      Set.Poly.of_list @@ Hash_set.to_list learned_clauses
    in
    let dep_graph = PCSP.Problem.dep_graph_of APCSP.problem in
    let res =
      match config.cex_strategy with
      | AllExamples ->
        (** for each (possibly parametric) candidate solution, for each clause,
            generate a (possibly parametric) counterexample *)
        let is_clause_must_satisfy =
          Clause.is_clause_must_satisfy @@
          Map.key_set @@ PCSP.Problem.partial_sol_targets_of APCSP.problem 
        in
        let rec iter examples = function
          | [] -> First examples
          | (cand, cand_tag) :: candidates ->
            if RLCfg.config.enable && RLCfg.config.show_candidates then
              Out_channel.print_endline @@ Printf.sprintf "candidate: %s" @@
              Yojson.Safe.to_string @@ Ast.CandSol.to_yojson cand;
            let clauses_must_satisfy =
              match cand_tag with
              | CandSol.Partial pvar ->
                let pvars = Map.Poly.find_exn dep_graph pvar in
                Set.Poly.filter clauses ~f:(is_clause_must_satisfy pvars)
              | _ -> clauses
            in
            let cexs = find_all_counterexamples clauses_must_satisfy fenv cand in
            if RLCfg.config.enable then begin
              let total = Set.Poly.length clauses_must_satisfy in
              let num_unsat = Set.Poly.length cexs in
              let num_sat = total - num_unsat in
              Out_channel.print_endline @@ "reward: " ^ string_of_int num_sat ^ "/" ^ string_of_int total;
              Out_channel.flush Out_channel.stdout
            end;
            let lbs_opt = if config.check_part_sol_with_lbs then Some (PCSP.Problem.senv_of APCSP.problem, fenv, VersionSpace.lower_bounds_of vs) else None in
            match cand_tag with
            | CandSol.Partial _ ->
              if config.check_part_sol_with_lbs || Set.Poly.is_empty cexs then
                (* if [check_part_sol_with_lbs] is false, the candidate is qualified as a partial solution if it satisfies the related clauses *)
                (* ToDo: in this case, the candidate is guaranteed to be a genuine partial solution? *)
                Messenger.send_candidate_partial_solution ~print:Debug.print messenger id (APCSP.problem, cexs, cand, cand_tag, lbs_opt, clauses_must_satisfy);
              iter examples candidates
            | Total with_sample ->
              if Set.Poly.is_empty cexs then Second cand
              else begin
                let examples' =
                  if with_sample then
                    Set.Poly.map cexs ~f:(fun (ex, srcs) ->
                        ExClause.normalize_params @@ ExClause.normalize ex, srcs)
                  else Set.Poly.empty
                in
                Messenger.send_candidate_partial_solution ~print:Debug.print messenger id (APCSP.problem, cexs, cand, cand_tag, lbs_opt, clauses_must_satisfy);
                iter (Set.Poly.union examples examples') candidates
              end
        in
        iter Set.Poly.empty candidates
      | ExamplesUpTo num_of_examples ->
        (** for each clause,
            generate up to [num_of_examples] counterexamples that are not satisfied by as much candidates as possible
        *)
        (** assume candidates are non-parametric *)
        let examples, spurious_cands =
          Set.Poly.fold clauses ~init:(Set.Poly.empty, Set.Poly.empty)
            ~f:(fun (examples, spurious_cands) clause ->
                let examples', spurious_cands' =
                  find_common_counterexamples_for_clause fenv num_of_examples candidates clause
                in
                let examples' = Set.Poly.map examples' ~f:(fun ex ->
                    ex, [ClauseGraph.Clause clause, false]) in
                Set.Poly.union examples examples',
                Set.Poly.union spurious_cands spurious_cands')
        in
        let is_genuine_solution cand = not @@ Set.Poly.mem spurious_cands cand in
        match List.find (List.map ~f:fst candidates) ~f:is_genuine_solution with
        | Some cand -> Second cand
        | None -> First examples
    in
    match res with
    | First examples ->
      print @@ lazy "******************************************";
      print @@ lazy "*** All the candidates are not genuine ***";
      print @@ lazy "******************************************\n";
      print @@ lazy "*** Counterexamples to the Candidate Solutions:";
      print @@ lazy
        (String.concat_set ~sep:";\n" @@
         Set.Poly.map ~f:(fun (ex, _) -> ExClause.str_of ex) examples);
      print @@ lazy "";
      Ok (State.of_examples vs examples)
    | Second sol ->
      print @@ lazy "*** a genuine solution is found: ";
      print @@ lazy (Ast.CandSol.str_of sol);
      Ok (State.Sat sol)

  let run_phase _iters e =
    if RLCfg.config.enable then begin
      if RLCfg.config.show_elapsed_time then Out_channel.print_endline "begin validator";
      let tm = Timer.make () in
      let res = State.Monad_infix.(Ok e >>=? validate) in
      if RLCfg.config.show_elapsed_time then Out_channel.print_endline (Format.sprintf "end validator: %f" (tm ()));
      res
    end else State.Monad_infix.(Ok e >>=? validate)
end

let make rl_config config pcsp =
  (module Make
       (struct let config = rl_config end)
       (struct let config = config end)
       (struct let problem = pcsp end) : ValidatorType)
