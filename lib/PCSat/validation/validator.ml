(** Validator *)

open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open PCSatCommon
open Ast

module type ValidatorType = sig
  val run_phase : int -> State.s -> State.u Or_error.t
end

(** configuration of validator *)
module Config = struct
  type cex_strategy = AllExamples | ExamplesUpTo of int [@@deriving yojson]

  type t = {
    verbose : bool;
    parametric_candidates : bool;
        (* whether parametric candidate solutions are enabled *)
    parametric_examples : bool; (* whether parametric examples are enabled *)
    strategy_synthesis : bool; (* require that parametric_examples = true*)
    smt_timeout : int option;
    cex_strategy : cex_strategy;
    check_part_sol_with_lbs : bool;
  }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let instantiate_ext_files cfg = Ok cfg

  let load_ext_file = function
    | ExtFile.Instance x -> Ok (ExtFile.Instance x)
    | Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
        | Error msg ->
            error_string
            @@ sprintf "Invalid Validator Configuration (%s): %s" filename msg)
end

module Make
    (RLCfg : RLConfig.ConfigType)
    (Cfg : Config.ConfigType)
    (APCSP : PCSP.Problem.ProblemType) : ValidatorType = struct
  let config = Cfg.config
  let id = PCSP.Problem.id_of APCSP.problem

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id

  let check_clause_nonparam_smt ?(timeout = None) fenv phi =
    let phi = Evaluator.simplify @@ LogicOld.Formula.mk_neg phi in
    Debug.print
    @@ lazy (sprintf "[check valid -> sat] %s" @@ LogicOld.Formula.str_of phi);
    Z3Smt.Z3interface.check_sat ~id ~timeout fenv [ phi ]

  let check_clause_param_smt ?(timeout = None) fenv params_senv uni_senv phi =
    let qphi =
      LogicOld.Formula.forall
        (Map.Poly.to_alist @@ Logic.to_old_sort_env_map uni_senv)
        phi
    in
    match Z3Smt.Z3interface.check_sat ~id ~timeout fenv [ qphi ] with
    | `Sat _model ->
        `Unsat (*ToDo: show model for parameters of the candidate solution *)
    | _ ->
        (* unsat, unknown, timeout*)
        let sub = Logic.to_old_dummies params_senv in
        check_clause_nonparam_smt fenv (LogicOld.Formula.subst sub phi)

  let check_clause_param_strat_synth ?(timeout = None) fenv params_senv uni_senv
      phi =
    let open QSMT.StrategySynthesis in
    let f =
      Evaluator.simplify @@ LogicOld.Formula.elim_ite
      @@ LogicOld.Formula.exists
           (Map.Poly.to_alist @@ Logic.to_old_sort_env_map params_senv)
      @@ LogicOld.Formula.forall
           (Map.Poly.to_alist @@ Logic.to_old_sort_env_map uni_senv)
      @@ LogicOld.Formula.aconv_tvar
           phi (*ToDo: this is necessary due to a bug?*)
    in
    (*print_endline @@ (sprintf "original input: %s\n" (LogicOld.Formula.str_of f));*)
    match LIA.formula_of_term @@ Logic.ExtTerm.of_old_formula f with
    | None ->
        (* f is possibly non-linear *)
        check_clause_param_smt ~timeout fenv params_senv uni_senv phi
    | Some f -> (
        (*Debug.print @@ lazy (sprintf "input: %s\n" (formula_to_string f));*)
        let p, s = LIAStrategySynthesis.nondet_strategy_synthesis f in
        (*Debug.print @@ lazy (sprintf "strategy skelton for %s:\n%s" (player_to_string p) (ssforest_to_string s));*)
        match p with
        | SAT ->
            `Unsat (*ToDo: show model for parameters of the candidate solution*)
        | UNSAT -> (
            let f = PreFormula.neg_formula LIA.neg_atom f in
            let fml, chc, det, params = LIAStrategySynthesis.loseCHC [] s f in
            (*Debug.print @@ lazy "strategy template:";
              Map.Poly.iteri det ~f:(fun ~key ~data:(senv, t) ->
              Debug.print @@ lazy
              (sprintf "%s: %s" (Ident.name_of_tvar key)
                (Logic.ExtTerm.str_of_term
                  (Map.force_merge (Map.Poly.of_alist_exn params) senv) t)));
              Debug.print @@ lazy "";*)
            let chc =
              ( Map.Poly.empty,
                Logic.ExtTerm.imply_of fml (Logic.BoolTerm.mk_bool false) )
              :: chc
            in
            let problem =
              PCSP.Problem.of_formulas
                ~params:(PCSP.Params.make @@ Map.of_list_exn params)
              @@ Set.Poly.of_list chc
            in
            (*Debug.print @@ lazy "recursion-free CHC problem for determinization:";
              Debug.print @@ lazy (PCSP.Problem.str_of problem);
              Debug.print @@ lazy "";*)
            match PCSP.ForwardPropagate.solve problem with
            | Ok (PCSP.Problem.Sat subs) ->
                (*Debug.print @@ lazy ("solution:\n" ^ Logic.str_of_term_subst Logic.ExtTerm.str_of subs);*)
                let ds =
                  Map.Poly.map det ~f:(fun (senv, t) ->
                      (senv, Logic.ExtTerm.subst subs t))
                in
                (*print_endline @@ (sprintf "determinized strategy for %s:"
                                    (player_to_string p));
                  Map.Poly.iteri ds ~f:(fun ~key ~data:(senv, t) ->
                    print_endline @@
                    (sprintf "%s: %s"
                       (Ident.name_of_tvar key)
                       (LogicOld.ExTerm.str_of_term params_senv(*ToDo*) senv t)));*)
                `Sat
                  (List.map (Map.Poly.to_alist ds) ~f:(fun (x, (senv, t)) ->
                       let t =
                         fix
                           ~f:(Logic.Term.subst (Map.Poly.map ds ~f:snd))
                           ~equal:Stdlib.( = ) t
                       in
                       ( (x, LogicOld.T_bool.SBool),
                         Some
                           (Logic.ExtTerm.to_old_term Map.Poly.empty senv t [])
                       )))
            | Ok (PCSP.Problem.Unsat _) -> assert false
            | Ok PCSP.Problem.Unknown -> assert false
            | Ok (PCSP.Problem.OutSpace _) -> assert false
            | Ok PCSP.Problem.Timeout -> assert false
            | Error err -> failwith (Error.to_string_hum err)))

  let find_all_counterexamples clauses fenv ((params_senv, cand) : CandSol.t) =
    let cand_map = CandSol.to_subst (params_senv, cand) in
    let cls_nonparam, cls_param =
      Set.partition_tf ~f:(fst >> Quintuple.trd >> Map.Poly.is_empty)
      @@ Set.Poly.map clauses ~f:(fun cl ->
             let uni_senv, clause = Clause.to_senv_formula cl in
             (*Debug.print @@ lazy ("size before: " ^ string_of_int @@ Logic.ExtTerm.ast_size clause);*)
             let phi = Logic.Term.subst cand_map clause in
             (*Debug.print @@ lazy ("size after: " ^ string_of_int @@ Logic.ExtTerm.ast_size phi);*)
             let phi =
               Logic.ExtTerm.to_old_fml Map.Poly.empty
                 (Map.force_merge params_senv uni_senv, phi)
             in
             let phi = Evaluator.simplify phi in
             let fvs = LogicOld.Formula.tvs_of phi in
             let uni_senv' = Map.Poly.filter_keys uni_senv ~f:(Set.mem fvs) in
             let params_senv' =
               Map.Poly.filter_keys params_senv ~f:(Set.mem fvs)
             in
             ( (uni_senv, clause, params_senv', uni_senv', phi),
               (ClauseGraph.Clause cl, true) ))
    in
    let cls_nonparam =
      Set.Poly.map cls_nonparam ~f:(fun ((uni_senv, clause, _, _, phi), cl) ->
          (* non-parametric candidate solution *)
          let result =
            check_clause_nonparam_smt ~timeout:config.smt_timeout fenv phi
          in
          (([ (uni_senv, clause) ], phi, result), [ cl ]))
    in
    let cls_param =
      Set.to_list cls_param
      |> List.classify (fun ((_, _, senv1, _, _), _) ((_, _, senv2, _, _), _) ->
             Fn.non Set.is_empty
             @@ Set.inter (Map.Poly.key_set senv1) (Map.Poly.key_set senv2))
      |> List.map ~f:(fun rs ->
             let (cls, params_senv', uni_senv', phi), cl =
               List.fold rs
                 ~init:
                   ( ( [],
                       Map.Poly.empty,
                       Map.Poly.empty,
                       LogicOld.Formula.mk_true () ),
                     [] )
                 ~f:(fun
                     ((cls, params_senv, uni_senv, phi), srcs)
                     ( (uni_senv0, clause0, params_senv', uni_senv', phi'),
                       src_cl )
                   ->
                   ( ( (uni_senv0, clause0) :: cls,
                       Map.force_merge params_senv params_senv',
                       Map.force_merge uni_senv uni_senv',
                       LogicOld.Formula.mk_and phi phi' ),
                     src_cl :: srcs ))
             in
             (* parametric candidate solution *)
             assert config.parametric_candidates;
             ( ( cls,
                 phi,
                 if config.strategy_synthesis then (
                   (* apply strategy synthesis to forall-exists formula *)
                   assert config.parametric_examples;
                   check_clause_param_strat_synth ~timeout:config.smt_timeout
                     fenv params_senv' uni_senv' phi)
                 else
                   (* apply SMT solving to forall-exists formula *)
                   check_clause_param_smt ~timeout:config.smt_timeout fenv
                     params_senv' uni_senv' phi ),
               cl ))
      |> Set.Poly.of_list
    in
    Set.union cls_nonparam cls_param
    |> Set.concat_map ~f:(fun ((cls, phi, res), src_cl) ->
           match res with
           | `Sat model ->
               (* not all but some clause in cls has a countermodel *)
               let res =
                 Set.Poly.union_list
                 @@ List.map cls ~f:(fun (uni_senv, clause) ->
                        let phi_clause =
                          Logic.ExtTerm.to_old_fml
                            (PCSP.Problem.senv_of APCSP.problem)
                            (uni_senv, clause)
                        in
                        ExClauseSet.of_model
                          (PCSP.Problem.senv_of APCSP.problem)
                          config.parametric_examples (uni_senv, phi_clause)
                          model)
               in
               if Fn.non Set.is_empty res then
                 Set.Poly.map res ~f:(fun ex -> (ex, src_cl))
               else
                 (* note that res never represents true *)
                 let ctx = Z3.mk_context [ ("MODEL", "true") ] in
                 let dtenv =
                   Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx
                     (PCSP.Problem.dtenv_of APCSP.problem)
                 in
                 Debug.print
                 @@ lazy
                      ("model: "
                      ^ LogicOld.str_of_model model
                      ^ "\ncandidate: "
                      ^ CandSol.str_of (params_senv, cand)
                      ^ "\nphi: "
                      ^ LogicOld.Formula.str_of phi
                      ^ "\nz3 input: " ^ Z3.Expr.to_string
                      @@ Z3Smt.Z3interface.of_formula ~id ctx [] [] fenv dtenv
                      @@ LogicOld.Formula.mk_neg phi);
                 (* ToDo: should be unreachable *)
                 (*dummy*)
                 Set.Poly.singleton
                 @@ ( ExClause.mk_unit_pos @@ ExAtom.mk_true (),
                      [ (ClauseGraph.Dummy, true) ] )
           | `Unsat -> Set.Poly.empty
           | _ ->
               (*failwith "Z3 reported unknown or timeout in the validation phase"*)
               (*dummy*)
               Set.Poly.singleton
               @@ ( ExClause.mk_unit_pos @@ ExAtom.mk_true (),
                    [ (ClauseGraph.Dummy, true) ] ))

  (** ToDo: fix to use real MaxSMT *)
  let find_common_counterexamples_for_clause fenv num_ex
      (candidates : (CandSol.t * CandSol.tag) list) clause =
    let exi_senv = PCSP.Problem.senv_of APCSP.problem in
    let uni_senv, clause = Clause.to_senv_formula clause in
    let cand_phi_list =
      List.map candidates ~f:(fun (cand, cand_tag) ->
          let cand_map = CandSol.to_subst cand in
          ( cand,
            ( cand_tag,
              LogicOld.Formula.mk_neg
              @@ Logic.ExtTerm.to_old_fml uni_senv
                   (Map.Poly.empty, Logic.Term.subst cand_map clause) ) ))
    in
    let spurious_cand_phi_list =
      List.filter cand_phi_list
        ~f:(snd >> snd >> Z3Smt.Z3interface.is_sat ~id fenv)
    in
    ( List.filter_map spurious_cand_phi_list ~f:(function
        | _, (CandSol.Total true, phi) -> Some phi
        | _ -> None)
      |> Z3Smt.Z3interface.max_smt_of ~id fenv num_ex
      |> Set.concat_map ~f:(fun model ->
             let examples =
               ExClauseSet.of_model exi_senv false
                 ( Map.force_merge exi_senv uni_senv,
                   Logic.ExtTerm.to_old_fml exi_senv (uni_senv, clause) )
                 model
             in
             assert (Fn.non Set.is_empty examples);
             examples),
      Set.Poly.of_list @@ List.map ~f:fst spurious_cand_phi_list )

  let receive_bounds vs =
    match PCSP.Problem.messenger_of APCSP.problem with
    | None -> ()
    | Some messenger ->
        let add =
          VersionSpace.add_bound_as_learned_clause ~print:Debug.print id
            APCSP.problem vs
        in
        Common.Messenger.receive_all_infos_with messenger id ~filter:(function
          | PCSP.Problem.(LowerBounds _ | UpperBounds _) -> true
          | _ -> false)
        |> List.iter ~f:(function
             | _, PCSP.Problem.LowerBounds bounds ->
                 Map.Poly.iteri bounds ~f:(fun ~key ~data -> add key data false)
             | _, PCSP.Problem.UpperBounds bounds ->
                 Map.Poly.iteri bounds ~f:(fun ~key ~data -> add key data true)
             | _ -> failwith "receive_bounds")

  let send_candidate_partial_solution vs cexs cand cand_tag cls =
    match PCSP.Problem.messenger_of APCSP.problem with
    | None -> ()
    | Some messenger -> (
        let lbs_opt =
          if config.check_part_sol_with_lbs then
            Some
              ( PCSP.Problem.senv_of APCSP.problem,
                VersionSpace.fenv_of vs,
                VersionSpace.lower_bounds_of vs )
          else None
        in
        let stable_clauses = PCSP.Problem.stable_clauses_of APCSP.problem in
        (*if Set.is_empty stable_clauses then ()(*ToDo*)
          else*)
        let violated_non_query_clauses =
          Set.concat_map cexs ~f:(fun (_, sources) ->
              (* filter out query clauses *)
              Set.Poly.of_list
              @@ List.filter_map sources ~f:(function
                   | ClauseGraph.Clause c, _
                     when not @@ Set.mem stable_clauses c ->
                       Some c
                   | _ -> None))
        in
        if Set.is_empty violated_non_query_clauses then
          (*let _ = assert (Set.is_singleton cexs && Stdlib.(=) (snd @@ Set.choose_exn cexs)[ClauseGraph.Dummy, true]) in*)
          (* reachable here if an SMT solving failed *) ()
        else
          let full_non_query_clauses = Set.diff cls stable_clauses in
          Debug.print
          @@ lazy
               (sprintf "full_non_query_clauses:\n%s\n"
               @@ String.concat_map_set ~sep:"\n" full_non_query_clauses
                    ~f:(Clause.str_of (PCSP.Problem.senv_of APCSP.problem)));
          Debug.print
          @@ lazy
               (sprintf "violated_non_query_clauses:\n%s\n"
               @@ String.concat_map_set ~sep:"\n" violated_non_query_clauses
                    ~f:(Clause.str_of (PCSP.Problem.senv_of APCSP.problem)));
          let sol = PCSP.Problem.sol_of_candidate APCSP.problem cand in
          let sol_before_red = CandSol.to_subst cand in
          match cand_tag with
          | CandSol.Partial target_pvar ->
              let partial_sol_cand_of =
                let pvars =
                  Set.Poly.map ~f:(fun ri -> ri.PCSP.Params.name)
                  @@ Map.Poly.find_exn
                       (PCSP.Problem.partial_sol_targets_of APCSP.problem)
                       target_pvar
                in
                fun sol -> Map.Poly.filter_keys sol ~f:(Set.mem pvars)
              in
              Debug.print
              @@ lazy
                   (sprintf
                      "send a candidate partial solution to the messenger for \
                       [%s]"
                   @@ Ident.name_of_tvar target_pvar);
              Common.Messenger.send_boardcast messenger id
              @@ PCSP.Problem.CandidateSolution
                   ( partial_sol_cand_of sol,
                     partial_sol_cand_of sol_before_red,
                     violated_non_query_clauses,
                     full_non_query_clauses,
                     lbs_opt )
          | Total _with_sampling ->
              let target_pvars =
                Map.key_set @@ PCSP.Problem.partial_sol_targets_of APCSP.problem
              in
              if Set.is_empty target_pvars then (
                (*ToDo: this case is necessary because [partial_sol_targets_of pfwcsp] is empty if [gen_extra_partial_sols] is false*)
                Debug.print
                @@ lazy "send a candidate partial solution to the messenger";
                Common.Messenger.send_boardcast messenger id
                @@ PCSP.Problem.CandidateSolution
                     ( sol,
                       sol_before_red,
                       violated_non_query_clauses,
                       full_non_query_clauses,
                       lbs_opt ))
              else if
                config.check_part_sol_with_lbs
                || (* if [check_part_sol_with_lbs] is false, necessary to satisfy [is_qualified_partial_solution] for some target pvar *)
                Set.exists target_pvars ~f:(fun pvar ->
                    PCSP.Problem.is_qualified_partial_solution
                      ~print:Debug.print
                      (Map.Poly.find_exn
                         (PCSP.Problem.dep_graph_of APCSP.problem)
                         pvar)
                      target_pvars violated_non_query_clauses)
              then (
                Debug.print
                @@ lazy "send a candidate partial solution to the messenger";
                Common.Messenger.send_boardcast messenger id
                @@ PCSP.Problem.CandidateSolution
                     ( sol,
                       sol_before_red,
                       violated_non_query_clauses,
                       full_non_query_clauses,
                       lbs_opt )))

  let validate vs (candidates : (CandSol.t * CandSol.tag) list) =
    Debug.print @@ lazy "**** Validator";
    Debug.print
    @@ lazy
         (String.concat_mapi_list ~sep:"\n" candidates
            ~f:(fun i (candidate, cand_tag) ->
              sprintf "**** %s candidate solution[%s] %s\n%s\n"
                (Ordinal.string_of @@ Ordinal.make i)
                (match cand_tag with
                | CandSol.Partial (Ident.Tvar key) ->
                    if config.check_part_sol_with_lbs then "LB_" ^ key else key
                | Total _ ->
                    if config.check_part_sol_with_lbs then "LB" else "-")
                (match cand_tag with
                | CandSol.Total true -> ""
                | _ -> "without sampling")
                (CandSol.str_of candidate)));
    receive_bounds vs;
    Debug.print
    @@ lazy
         (VersionSpace.str_of_learned_clauses
            (PCSP.Problem.senv_of APCSP.problem)
         @@ VersionSpace.learned_clauses_of vs);
    let clauses =
      Set.union (PCSP.Problem.clauses_of APCSP.problem)
      @@ Set.Poly.of_list @@ Hash_set.to_list
      @@ VersionSpace.learned_clauses_of vs
    in
    let res =
      match config.cex_strategy with
      | AllExamples ->
          (* for each (possibly parametric) candidate solution, for each clause,
              generate a (possibly parametric) counterexample *)
          let is_hard =
            Clause.must_be_satisfied ~print:Debug.print
            @@ Map.key_set
            @@ PCSP.Problem.partial_sol_targets_of APCSP.problem
          in
          let rec iter examples = function
            | [] -> First examples
            | (cand, cand_tag) :: candidates -> (
                if RLCfg.config.enable && RLCfg.config.show_candidates then (
                  RLConfig.lock ();
                  Debug.print_stdout
                  @@ lazy
                       (sprintf "candidate: %s" @@ Yojson.Safe.to_string
                      @@ CandSol.to_yojson cand);
                  RLConfig.unlock ());
                let hard_clauses =
                  match cand_tag with
                  | CandSol.Partial pvar ->
                      let pvs =
                        Map.Poly.find_exn
                          (PCSP.Problem.dep_graph_of APCSP.problem)
                          pvar
                      in
                      Set.filter clauses ~f:(is_hard pvs)
                  | _ -> clauses
                in
                let cexs =
                  find_all_counterexamples hard_clauses
                    (VersionSpace.fenv_of vs) cand
                in
                if RLCfg.config.enable then (
                  RLConfig.lock ();
                  let total = Set.length hard_clauses in
                  let num_unsat = Set.length cexs in
                  let num_sat = total - num_unsat in
                  Debug.print_stdout
                  @@ lazy
                       (sprintf "reward: %s/%s" (string_of_int num_sat)
                          (string_of_int total));
                  Out_channel.flush Out_channel.stdout;
                  RLConfig.unlock ());
                match cand_tag with
                | CandSol.Partial _ ->
                    if config.check_part_sol_with_lbs || Set.is_empty cexs then
                      (* if [check_part_sol_with_lbs] is false, the candidate is qualified as a partial solution if it satisfies the related clauses *)
                      (* ToDo: in this case, the candidate is guaranteed to be a genuine partial solution? *)
                      send_candidate_partial_solution vs cexs cand cand_tag
                        hard_clauses;
                    iter examples candidates
                | Total with_sampling ->
                    if Set.is_empty cexs then Second cand
                    else (
                      send_candidate_partial_solution vs cexs cand cand_tag
                        hard_clauses;
                      let examples' =
                        if with_sampling then
                          let unknowns =
                            Map.key_set @@ PCSP.Problem.senv_of APCSP.problem
                          in
                          Set.union examples
                          @@ Set.Poly.map cexs ~f:(fun (ex, srcs) ->
                                 ( ExClause.normalize_params unknowns
                                   @@ ExClause.normalize ex,
                                   srcs ))
                        else examples
                      in
                      iter examples' candidates))
          in
          iter Set.Poly.empty candidates
      | ExamplesUpTo num_of_examples -> (
          (* for each clause,
              generate up to [num_of_examples] counterexamples that are not satisfied by as much candidates as possible
          *)
          (* assume candidates are non-parametric *)
          let examples, spurious_cands =
            Set.fold clauses ~init:(Set.Poly.empty, Set.Poly.empty)
              ~f:(fun (examples, spurious_cands) cl ->
                let examples', spurious_cands' =
                  find_common_counterexamples_for_clause
                    (VersionSpace.fenv_of vs) num_of_examples candidates cl
                in
                let examples' =
                  Set.Poly.map examples' ~f:(fun ex ->
                      (ex, [ (ClauseGraph.Clause cl, false) ]))
                in
                ( Set.union examples examples',
                  Set.union spurious_cands spurious_cands' ))
          in
          let is_genuine_solution cand = not @@ Set.mem spurious_cands cand in
          match
            List.find (List.map ~f:fst candidates) ~f:is_genuine_solution
          with
          | None -> First examples
          | Some cand -> Second cand)
    in
    match res with
    | First examples ->
        Debug.print @@ lazy "******************************************";
        Debug.print @@ lazy "*** All the candidates are not genuine ***";
        Debug.print @@ lazy "******************************************\n";
        Debug.print @@ lazy "*** Counterexamples to the Candidate Solutions:";
        Debug.print
        @@ lazy
             (String.concat_set ~sep:";\n"
             @@ Set.Poly.map ~f:(fst >> ExClause.str_of) examples);
        Debug.print @@ lazy "";
        Ok (State.of_examples vs examples)
    | Second sol ->
        Debug.print @@ lazy "*** a genuine solution is found: ";
        Debug.print @@ lazy (CandSol.str_of sol);
        Ok (State.Sat sol)

  let run_phase _iters e =
    if RLCfg.config.enable then (
      if RLCfg.config.show_elapsed_time then (
        RLConfig.lock ();
        Debug.print_stdout @@ lazy "begin validator";
        RLConfig.unlock ());
      let tm = Timer.make () in
      let res = State.Monad_infix.(Ok e >>=? validate) in
      if RLCfg.config.show_elapsed_time then (
        RLConfig.lock ();
        Debug.print_stdout @@ lazy (sprintf "end validator: %f" (tm ()));
        RLConfig.unlock ());
      res)
    else State.Monad_infix.(Ok e >>=? validate)
end

let make rl_config config pcsp =
  (module Make
            (struct
              let config = rl_config
            end)
            (struct
              let config = config
            end)
            (struct
              let problem = pcsp
            end) : ValidatorType)
