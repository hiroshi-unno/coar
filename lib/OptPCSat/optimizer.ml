open Core
open Ast
open Ast.Ident
open Ast.Logic
open Common
open Common.Ext
open Common.Util
open Common.Messenger
open Common.Combinator
open Preprocessing

module type OptimizerType = sig
  val optimize :
    ?filename:string option ->
    Ident.tvar list ->
    PCSP.Problem.t ->
    CHCOpt.Problem.solution * int
end

module Make
    (Solver : PCSPSolver.Solver.SolverType)
    (MaximalityChecker : OptimalityChecker.OptimalityCheckerType)
    (MinimalityChecker : OptimalityChecker.OptimalityCheckerType)
    (NonOptChecker : NonOptChecker.NonOptCheckerType)
    (Cfg : Config.ConfigType) : OptimizerType = struct
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_module_name "Optimizer"
  let enable_parallel = true

  (* for sequential optimizer *)
  let num_improved = ref 0
  let improve_until = 0
  let mutex = Caml_threads.Mutex.create ()
  let lock () = Caml_threads.Mutex.lock mutex
  let unlock () = Caml_threads.Mutex.unlock mutex

  module Preprocessor = Preprocessor.Make (struct
    let config = Preprocessor.Config.make true config.verbose 4 0 true
  end)

  let old_theta = Hashtbl.Poly.create ()
  let extract_tuple pcsp = TupleExtracter.extract_tuples pcsp

  let preprocessor bpvs pcsp =
    lock ();
    let pcsp = extract_tuple pcsp in
    Debug.print_log
    @@ lazy
         (sprintf
            "***************************** Preprocessor \
             *****************************\n");
    let pcsp' = ref pcsp in
    (try
       ignore
       @@ Preprocessor.solve ~bpvs:(Set.Poly.of_list bpvs)
            (fun ?(oracle = None) pcsp ->
              ignore oracle;
              pcsp' := pcsp;
              Or_error.unimplemented "")
            pcsp
     with _ -> ());
    Debug.print_log
    @@ lazy
         (sprintf
            "***************************** preprocessed CHCs \
             *****************************\n\
             %s"
         @@ PCSP.Problem.str_of !pcsp');
    unlock ();
    !pcsp'

  let old_formula_of_sol senv args sol =
    let sol = ExtTerm.beta_reduction (Term.mk_apps sol args) in
    (* Debug.print_log ~tag:(name_of_tvar p) @@ ExtTerm.str_of sol; *)
    ExtTerm.to_old_fml Map.Poly.empty (Map.Poly.of_alist_exn senv, sol)

  let equiv_old_sol_of (p : tvar) (sol : term) =
    match Hashtbl.Poly.find old_theta p with
    | Some old_sol ->
        let senv, _ = ExtTerm.let_lam sol in
        let args = List.map ~f:(fst >> ExtTerm.mk_var) senv in
        let equiv =
          let phi1 = old_formula_of_sol senv args sol in
          let phi2 = old_formula_of_sol senv args old_sol in
          LogicOld.Formula.(and_of [ mk_imply phi1 phi2; mk_imply phi2 phi1 ])
        in
        (* Debug.print_log ~tag:("check equiv old sol:" ^ (name_of_tvar p)) @@ LogicOld.Formula.str_of equiv; *)
        if Z3Smt.Z3interface.is_valid ~id:None (LogicOld.get_fenv ()) equiv then
          (* let _ = Debug.print_log"yes" in *)
          old_sol
        else (
          (* let _ = Debug.print_log"no" in *)
          Hashtbl.Poly.set old_theta ~key:p ~data:sol;
          sol)
    | _ ->
        Hashtbl.Poly.set old_theta ~key:p ~data:sol;
        sol

  let simplify_theta delta =
    Map.Poly.mapi ~f:(fun ~key:p ~data:sol ->
        let senv, _ = ExtTerm.let_lam sol in
        let args = List.map ~f:(fst >> ExtTerm.mk_var) senv in
        let fenv = LogicOld.get_fenv () in
        let sol = ExtTerm.beta_reduction (Term.mk_apps sol args) in
        (* Debug.print_log ~tag:(name_of_tvar p) @@ ExtTerm.str_of sol; *)
        ExtTerm.to_old_fml delta (Map.Poly.of_alist_exn senv, sol)
        (* |> (fun phi -> Debug.print_log ~tag:"1" @@ LogicOld.Formula.str_of phi; phi) *)
        |> Evaluator.simplify
        |> Normalizer.normalize
        (* |> Z3Smt.Z3interface.z3_simplify ~id:(Some 0) fenv *)
        |> (fun phi ->
             match
               Evaluator.check
                 (Z3Smt.Z3interface.is_valid ~id:(Some 0) fenv)
                 phi
             with
             | Some true -> LogicOld.Formula.mk_true ()
             | Some false -> LogicOld.Formula.mk_false ()
             | None -> phi)
        |> Z3Smt.Z3interface.simplify ~id:(Some 0) fenv ~timeout:(Some 20000)
        (* |> (fun phi -> Debug.print_log ~tag:"2" @@ LogicOld.Formula.str_of phi; phi) *)
        |> ExtTerm.of_old_formula
        |> ExtTerm.mk_lambda senv |> equiv_old_sol_of p)

  let remove_unused_params pcsp =
    PCSP.Problem.update_params pcsp
    @@ {
         (PCSP.Problem.params_of pcsp) with
         PCSP.Params.sol_for_eliminated = Map.Poly.empty;
         PCSP.Params.args_record = Map.Poly.empty;
       }

  let _qelim ~id delta phi =
    let open LogicOld in
    let clauses =
      Formula.cnf_of (to_old_sort_env_map delta) @@ Formula.nnf_of phi
    in
    Set.Poly.map clauses ~f:(fun (ps, ns, pure_phi) ->
        let tvs = Set.concat_map ~f:Atom.tvs_of @@ Set.union ps ns in
        let sort_env =
          Formula.sort_env_of pure_phi
          |> Set.filter ~f:(fst >> Set.mem tvs >> not)
          |> Set.to_list
        in
        let pure_phi =
          Formula.mk_forall sort_env pure_phi
          |> Z3Smt.Z3interface.qelim ~id ~fenv:(LogicOld.get_fenv ())
          |> fun phi ->
          Debug.print_log ~tag:"qelimed" @@ lazy (Formula.str_of phi);
          if Formula.is_bind phi then pure_phi else phi
        in
        snd @@ ClauseOld.to_formula (Map.Poly.empty, ps, ns, pure_phi))
    |> Set.to_list |> Formula.and_of

  let extend_pcsp_with (messenger, id) pcsp delta c nepvs =
    let delta = Map.force_merge nepvs delta in
    let params =
      let params = PCSP.Problem.params_of pcsp in
      let kind_map =
        params.kind_map |> Kind.add_kinds (Map.Poly.key_set nepvs) Kind.NE
      in
      PCSP.Params.make ~dtenv:params.dtenv ~kind_map ~fenv:params.fenv
        ~sol_space:params.sol_space ~id
        ~sol_for_eliminated:params.sol_for_eliminated ~messenger delta
    in
    c |> ExtTerm.nnf_of
    |> ExtTerm.cnf_of delta Map.Poly.empty
    |> Set.Poly.map ~f:(fun (_, _, phi) ->
           let uni_senv, _, phi =
             LogicOld.Formula.skolemize ~use_fn_pred:false ~only_impure:true
             @@ ExtTerm.to_old_fml delta (Map.Poly.empty, phi)
           in
           ExtTerm.of_old (uni_senv, phi))
    |> Set.union @@ PCSP.Problem.formulas_of pcsp
    |> PCSP.Problem.of_formulas ~params

  let check_optimality ?(only_simple = false) (messenger, id) pcsp delta theta
      priority pvar =
    Debug.print_log
    @@ lazy
         (sprintf
            "************************* Optimality Checking Start (%s) \
             **************************\n"
         @@ name_of_tvar pvar);
    (* let PCSP.Problem.update_params  *)
    let pcsp =
      PCSP.Problem.map_params pcsp ~f:(fun params ->
          { params with PCSP.Params.id })
    in
    let pcsp =
      if not only_simple then
        PCSP.Problem.subst ~bpvs:(Set.Poly.singleton pvar) ~elim:false theta
          pcsp
        |> preprocessor priority
      else pcsp
    in
    let res =
      (if NonOptChecker.is_dup pvar then MaximalityChecker.check
       else MinimalityChecker.check (*ToDo*))
        ~only_simple (messenger, id) pvar pcsp delta theta
    in
    (match res with
    | CHCOpt.Problem.OptSat _ ->
        Debug.print_log
        @@ lazy (sprintf "*** Optimality Checking Result: Optimal!\n");
        Debug.print_log
        @@ lazy
             (sprintf
                "************************* Optimality Checking End (%s) \
                 **************************\n"
             @@ name_of_tvar pvar)
    | CHCOpt.Problem.Unknown -> () (* optimality unknown *)
    | _ ->
        failwith
          "maximality and minimality checkers only return OptSat or Unknown");
    res

  let clean () =
    Debug.print_log @@ lazy "clean evaluator cache";
    Evaluator.clean ();
    (* Debug.print_log @@ lazy "clean z3"; Z3Smt.Z3interface.clean (); *)
    (* Debug.print_log @@ lazy "gc.compact"; Gc.compact (); *)
    Debug.print_log @@ lazy "gc.full_major";
    Gc.full_major ();
    Debug.print_log @@ lazy "clean over";
    ignore @@ Core_unix.nanosleep 0.5

  let improve (messenger, id) improved full_priority priority pcsp delta theta =
    let theta = simplify_theta delta theta in
    let c, nepvs =
      NonOptChecker.improve delta
        (if config.improve_current then full_priority else priority)
        theta
    in
    let phi =
      ExtTerm.to_old_fml (Map.force_merge delta nepvs) (Map.Poly.empty, c)
    in
    let bpvs =
      Map.Poly.keys nepvs @ full_priority
      |> Set.Poly.of_list
      |> Set.filter ~f:(Fn.non @@ Set.mem improved)
    in
    Debug.print_log ~tag:"improve"
    @@ lazy (sprintf "a pnCSP generated: %s" @@ LogicOld.Formula.str_of phi);
    let pcsp' =
      extend_pcsp_with (messenger, id) pcsp delta
        (ExtTerm.of_old_formula @@ Evaluator.simplify phi)
        nepvs
    in
    let pcsp' =
      let maxcs =
        (*ToDo: necessary?*)
        Set.Poly.map improved ~f:(fun v ->
            Debug.print_log ~tag:"improved" @@ lazy (Ident.name_of_tvar v);
            NonOptChecker.gen_maxc delta v theta)
      in
      let params = PCSP.Problem.params_of pcsp' in
      let phis = PCSP.Problem.formulas_of pcsp' in
      PCSP.Problem.of_formulas ~params (Set.union phis maxcs)
    in
    Debug.print_log
    @@ lazy
         (sprintf
            "***************************** Improving Start (%s) \
             *****************************\n"
         @@ String.concat_map_list ~sep:"," priority ~f:name_of_tvar);
    let sol =
      match Solver.solve ~bpvs pcsp' with
      | Ok (PCSP.Problem.Unsat _, _) -> CHCOpt.Problem.OptSat theta
      | Ok (PCSP.Problem.Unknown, _) -> CHCOpt.Problem.Unknown
      | Ok (PCSP.Problem.OutSpace _, _) -> CHCOpt.Problem.OptSatInSpace theta
      | Ok (PCSP.Problem.Timeout, _) -> CHCOpt.Problem.Timeout
      | Ok (PCSP.Problem.Sat theta', _) ->
          let theta' =
            Map.key_set delta
            |> Map.restrict
                 ~def:(fun p ->
                   let senv =
                     mk_fresh_sort_env_list @@ Sort.args_of
                     @@ Map.Poly.find_exn delta p
                   in
                   ExtTerm.mk_lambda senv @@ ExtTerm.mk_bool true)
                 theta'
            |> simplify_theta delta
          in
          (* a strictly improved solution found *)
          CHCOpt.Problem.Sat theta'
      | exception Terminated -> raise Terminated
      | Error err -> raise (Error.to_exn err)
    in
    Debug.print_log
    @@ lazy
         (sprintf
            "***************************** Improving End (%s) \
             *****************************\n"
         @@ String.concat_map_list ~sep:"," priority ~f:name_of_tvar);
    sol

  let task_pool = Task.setup_pool ~num_additional_domains:2

  let parallel_check_opt improved full_priority priority pcsp delta theta =
    match
      check_optimality ~only_simple:true (None, Some 0) pcsp delta theta
        priority (List.hd_exn priority)
    with
    | OptSat _ as sol -> sol
    | _ ->
        let messenger = Common.Messenger.create 2 in
        let send_terminate src dst =
          send_request messenger src dst Common.Messenger.Terminate;
          Debug.print_log ~tag:"sender" @@ lazy "send terminate"
        in
        let improve_task_id = PCSP.Params.new_id () in
        let optimality_check_id = PCSP.Params.new_id () in
        let optimality_check_task =
          Task.async task_pool (fun () ->
              match
                check_optimality
                  (Some messenger, optimality_check_id)
                  pcsp delta theta priority (List.hd_exn priority)
              with
              | CHCOpt.Problem.Unknown ->
                  (CHCOpt.Problem.Skip, optimality_check_id)
              | CHCOpt.Problem.OptSat sol ->
                  send_terminate optimality_check_id improve_task_id;
                  (CHCOpt.Problem.OptSat sol, optimality_check_id)
              | _ -> failwith "only OptSat and Unknown are reachable"
              | exception Common.Messenger.Terminated ->
                  Debug.print_log @@ lazy "optimality_check_task terminated";
                  (* receive_request_for_terminated optimality_check_id; *)
                  (CHCOpt.Problem.Skip, optimality_check_id)
              | exception e ->
                  Printexc.print_backtrace Out_channel.stderr;
                  raise e)
        in
        let improve_task =
          Task.async task_pool (fun () ->
              match
                improve
                  (Some messenger, improve_task_id)
                  improved full_priority priority pcsp delta theta
              with
              | CHCOpt.Problem.Unknown -> (CHCOpt.Problem.Skip, improve_task_id)
              | sol (* only OptSat, OptSatInSpace, and Sat are reachable *) ->
                  send_terminate improve_task_id optimality_check_id;
                  (sol, improve_task_id)
              | exception Common.Messenger.Terminated ->
                  Debug.print_log @@ lazy "improve_task terminated";
                  (* receive_request_for_terminated improve_task_id; *)
                  (CHCOpt.Problem.Skip, improve_task_id)
              | exception e ->
                  Printexc.print_backtrace Out_channel.stderr;
                  raise e)
        in
        let wait_other_task id =
          match
            if Stdlib.(id = improve_task_id) then
              Task.await task_pool optimality_check_task
            else Task.await task_pool improve_task
          with
          | sol -> sol
          | exception e ->
              Printexc.print_backtrace Out_channel.stderr;
              raise e
        in
        Debug.print_log ~tag:"parallel_check_opt" @@ lazy "start!";
        let sol =
          match
            Task.await_any_promise task_pool
              [ improve_task; optimality_check_task ]
          with
          | Skip, id ->
              Debug.print_log
              @@ lazy
                   "One task finished with a useless result. Wait for the \
                    other task to complete.";
              fst @@ wait_other_task id
          | sol, id ->
              Debug.print_log
              @@ lazy
                   "One task finished. Wait for the other task to be \
                    terminated.";
              ignore @@ wait_other_task id;
              sol
          | exception e -> raise e
        in
        clean ();
        sol

  let sequential_check_opt improved full_priority priority pcsp delta theta =
    match
      check_optimality ~only_simple:true
        (None, PCSP.Params.new_id ())
        pcsp delta theta priority (List.hd_exn priority)
    with
    | CHCOpt.Problem.OptSat sol -> CHCOpt.Problem.OptSat sol
    | _ -> (
        if !num_improved < improve_until then
          improve (None, Some 0) improved full_priority priority pcsp delta
            theta
        else
          match
            check_optimality
              (None, PCSP.Params.new_id ())
              pcsp delta theta priority (List.hd_exn priority)
          with
          | OptSat sol -> OptSat sol
          | _ ->
              improve (None, Some 0) improved full_priority priority pcsp delta
                theta)

  let check_opt =
    if enable_parallel then parallel_check_opt else sequential_check_opt

  let rec optimize_aux iter improved full_priority priority pcsp delta theta =
    let theta = simplify_theta delta theta in
    Debug.print_log
    @@ lazy
         (sprintf "Optimizing the current candidate for %s:\n%s\n"
            (String.concat_map_list ~sep:"," priority ~f:name_of_tvar)
         @@ CandSol.str_of
         @@ CandSol.of_subst delta theta);
    print_endline
    @@ sprintf "[%s] %s\n"
         (String.concat_map_list ~sep:"," priority ~f:name_of_tvar)
    @@ CHCOpt.Problem.str_of_solution delta iter
    @@ Sat theta;
    match check_opt improved full_priority priority pcsp delta theta with
    | Sat theta' ->
        num_improved := !num_improved + 1;
        optimize_aux (iter + 1) improved full_priority priority pcsp delta
          theta'
    | sol -> (sol, iter)

  let add_side_conditions priority pcsp =
    let senv = PCSP.Problem.senv_of pcsp in
    if
      not
        (Config.is_non_trival_mode config.mode
        || Config.is_non_vacuous_mode config.mode)
    then pcsp
    else
      let nesenv1, neclause1 =
        List.map priority ~f:(fun v ->
            let sort = Map.Poly.find_exn senv v in
            let args, param_senv = OptimalityChecker.mk_fresh_args sort in
            let pne = Ident.mk_ne_tvar v in
            let body = ExtTerm.mk_var_app pne args in
            let head = ExtTerm.mk_var_app v args in
            let param_senv = Map.Poly.of_alist_exn param_senv in
            ( (pne, sort),
              ExtTerm.imply_of body head |> ExtTerm.nnf_of
              |> ExtTerm.cnf_of senv param_senv
              |> Set.Poly.map ~f:(fun (ps, ns, phi) ->
                     (param_senv, ps, ns, phi)) ))
        |> List.unzip
        |> fun (nesenv, cls) -> (nesenv, Set.Poly.union_list cls)
      in
      let nesenv2, neclause2 =
        if Config.is_non_trival_mode config.mode then ([], Set.Poly.empty)
        else
          PCSP.Problem.clauses_of @@ pcsp
          |> Set.filter ~f:(fun (_, ps, ns, _) ->
                 Fn.non Set.is_empty ps && Fn.non Set.is_empty ns)
          |> Set.to_list
          |> List.filter_mapi ~f:(fun i (param_senv, _, ns, phi) ->
                 let pvs =
                   Set.to_list @@ Set.Poly.map ns ~f:ExtTerm.let_var_app
                 in
                 if
                   (not
                      (List.for_all pvs ~f:(fun (v, _) ->
                           List.exists priority ~f:(Stdlib.( = ) v))))
                   || (Set.length ns <= 1 && ExtTerm.is_bool phi)
                 then None
                 else
                   let pne =
                     OptimalityChecker.pn (mk_ne_tvar (Tvar "non_vac")) i
                   in
                   let tvs =
                     ExtTerm.fvs_of @@ ExtTerm.and_of @@ (phi :: Set.to_list ns)
                     |> Set.filter ~f:(Map.Poly.mem param_senv)
                     |> Set.Poly.map ~f:ExtTerm.mk_var
                     |> Set.to_list
                     |> List.sort ~compare:Stdlib.compare
                   in
                   let sargs =
                     List.map tvs
                       ~f:
                         (ExtTerm.let_var >> fst >> Map.Poly.find_exn param_senv)
                   in
                   let body = ExtTerm.mk_var_app pne tvs in
                   let head =
                     ExtTerm.and_of (ExtTerm.neg_of phi :: Set.to_list ns)
                   in
                   let clause =
                     ExtTerm.imply_of body head |> ExtTerm.nnf_of
                     |> ExtTerm.cnf_of senv param_senv
                     |> Set.Poly.map ~f:(fun (ps, ns, phi) ->
                            (param_senv, ps, ns, phi))
                   in
                   Some ((pne, Sort.mk_fun (sargs @ [ ExtTerm.SBool ])), clause))
          |> List.unzip
          |> fun (nesenv, cls) -> (nesenv, Set.Poly.union_list cls)
      in
      let nesenv = Map.Poly.of_alist_exn (nesenv1 @ nesenv2) in
      let kind_map = Map.Poly.map nesenv ~f:(fun _ -> Kind.NE) in
      let params = PCSP.Problem.params_of pcsp in
      let params =
        {
          params with
          kind_map = Map.force_merge params.kind_map kind_map;
          senv = Map.force_merge params.senv nesenv;
        }
      in
      Set.Poly.union_list [ neclause1; neclause2; PCSP.Problem.clauses_of pcsp ]
      |> PCSP.Problem.of_clauses ~params
      |> PCSP.Problem.formulas_of
      |> PCSP.Problem.of_formulas ~params

  let optimize ?(filename = None) full_priority pcsp =
    Debug.print_log ~tag:"optimization priority"
    @@ lazy (String.concat_map_list ~sep:"," full_priority ~f:name_of_tvar);
    let src_pcsp_wo_side_conds =
      pcsp |> preprocessor full_priority |> PCSP.Problem.merge_clauses
      |> preprocessor full_priority |> remove_unused_params
    in
    let src_pcsp =
      src_pcsp_wo_side_conds
      |> add_side_conditions full_priority
      |> preprocessor full_priority |> remove_unused_params
    in
    let delta = PCSP.Problem.senv_of src_pcsp in
    (* find an intial solution of [pcsp] *)
    let src_pcsp =
      PCSP.Problem.update_params src_pcsp
        { (PCSP.Problem.params_of src_pcsp) with id = Some 0 }
    in
    let init_sol =
      let sol_opt =
        if config.load_init_sol then
          Option.(
            filename >>= fun filename ->
            let basename =
              fst @@ Filename.split_extension @@ snd @@ Filename.split filename
            in
            let filename = "./" ^ basename ^ ".sol" in
            match SyGuS.Parser.solution_from_file filename with
            | Ok defs -> Some (Map.Poly.of_alist_exn defs)
            | Error _ -> failwith @@ sprintf "failed to load %s" filename)
        else None
      in
      match sol_opt with
      | None -> Solver.solve ~bpvs:(Set.Poly.of_list full_priority) src_pcsp
      | Some sol -> Ok (PCSP.Problem.Sat sol, 0 (*dummy*))
    in
    match init_sol with
    | Ok (PCSP.Problem.Unsat _, _) -> (CHCOpt.Problem.Unsat, 0)
    | Ok (PCSP.Problem.Unknown, _) -> (CHCOpt.Problem.Unknown, 0)
    | Ok (PCSP.Problem.OutSpace _, _) -> (CHCOpt.Problem.Unknown, 0 (*ToDo*))
    | Ok (PCSP.Problem.Timeout, _) -> (CHCOpt.Problem.Timeout, 0)
    | Ok (PCSP.Problem.Sat theta, _) ->
        let src_pcsp =
          if config.improve_current then src_pcsp_wo_side_conds else src_pcsp
        in
        if config.one_by_one then
          let rec inner max_in_space iter improved priority pcsp theta =
            match priority with
            | [] ->
                ( (if max_in_space then CHCOpt.Problem.OptSatInSpace theta
                   else CHCOpt.Problem.OptSat theta),
                  iter )
            | p :: priority' -> (
                Debug.print_log
                @@ lazy
                     (sprintf
                        "***************************** begin optimization for \
                         %s *****************************\n"
                     @@ name_of_tvar p);
                let res =
                  num_improved := 0;
                  optimize_aux iter improved full_priority [ p ] pcsp delta
                    theta
                in
                Debug.print_log
                @@ lazy
                     (sprintf
                        "*****************************   end optimization for \
                         %s *****************************\n"
                     @@ name_of_tvar p);
                match res with
                | Skip, iter -> (Unknown, iter (*ToDo*))
                | OptSat theta, iter | OptSatInSpace theta, iter ->
                    Debug.print_log
                      ~tag:
                        (sprintf "Optimization for (%s) is over"
                        @@ name_of_tvar p)
                    @@ lazy
                         (sprintf "The current candidate:\n%s"
                         @@ CandSol.str_of
                         @@ CandSol.of_subst delta theta);
                    Solver.reset ();
                    let improved = Set.add improved p in
                    let pcsp =
                      if true then pcsp
                      else
                        PCSP.Problem.subst ~elim:false
                          (Map.Poly.filter_keys theta ~f:(Set.mem improved))
                          pcsp
                        |> preprocessor priority
                    in
                    inner
                      (match res with
                      | OptSatInSpace _, _ -> true
                      | _ -> max_in_space)
                      iter improved priority' pcsp theta
                | _ -> failwith "inner")
          in
          inner false 0 Set.Poly.empty full_priority src_pcsp theta
        else (
          num_improved := 0;
          optimize_aux 0 Set.Poly.empty full_priority full_priority src_pcsp
            delta theta)
    | Error err -> failwith @@ Stdlib.Printexc.to_string @@ Error.to_exn err
end

let make (config : Config.t) improver =
  let (module Solver : PCSPSolver.Solver.SolverType) =
    match ExtFile.unwrap config.improve_solver with
    | Ok cfg -> PCSPSolver.Solver.make cfg
    | Error exn -> Error.raise exn
  in
  let (module NonOptChecker : NonOptChecker.NonOptCheckerType) = improver in
  let (module MaximalityChecker : OptimalityChecker.OptimalityCheckerType) =
    MaximalityChecker.make config
  in
  let (module MinimalityChecker : OptimalityChecker.OptimalityCheckerType) =
    MinimalityChecker.make config
  in
  (module Make (Solver) (MaximalityChecker) (MinimalityChecker) (NonOptChecker)
            (struct
              let config = config
            end) : OptimizerType)
