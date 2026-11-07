(* OptPCSat's optimization loop, after Yu Gu, Takeshi Tsukada and Hiroshi
   Unno, "Optimal CHC Solving via Termination Proofs", POPL 2023.

   [optimize] preprocesses the problem (tuples flattened, optional
   side conditions added), finds an initial solution with the improvement
   solver (or checks a seed solution read beside the input, falling back to
   solving when the seed violates a constraint), and then repeats rounds
   until a round finds no better solution.  A round runs an optimality check
   of the current solution for the next predicate, by the maximality or
   minimality checker, which reduces it to a termination problem, and an
   improvement step, which asks the constraint solver for a strictly better
   solution.  The two run in parallel domains each round, and the first
   decisive answer ends it.  [OptSat] comes from the improver's [unsat] for
   the improvement constraint or from the checker's certificate.  A
   certificate that is not known to be exact (it may have fixed the other
   predicates too strongly) is offered to the improver for a bounded wait,
   and is accepted when the improver finds no better solution in that
   time, so such an answer rests on the checker alone. *)
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
    (* every preprocessing field not given here takes its default, as on the
       constraint solver's own entry point *)
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
     with exn_ when not (Common.Timer.is_async exn_) -> ());
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
    ExtTerm.to_old_fml Map.Poly.empty (Map.Poly.of_alist_exn senv) sol

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
        ExtTerm.to_old_fml delta (Map.Poly.of_alist_exn senv) sol
        (* |> (fun phi -> Debug.print_log ~tag:"1" @@ LogicOld.Formula.str_of phi; phi) *)
        |> Evaluator.simplify
        |> Normalizer.normalize
        (* |> Z3Smt.Z3interface.z3_simplify ~id:(Some 0) fenv *)
        |> (fun phi ->
        match
          Evaluator.check (Z3Smt.Z3interface.is_valid ~id:(Some 0) fenv) phi
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
      {
        (PCSP.Problem.params_of pcsp) with
        PCSP.Params.sol_for_eliminated = Map.Poly.empty;
        sol_for_resolved = Map.Poly.empty;
        erasure_trail = Map.Poly.empty;
        PCSP.Params.args_record = Map.Poly.empty;
      }

  let _qelim ~id delta phi =
    let open Ast.LogicOld in
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
        params.kind_map |> Kind.add_kinds (Map.Poly.key_set nepvs) (Kind.Tot [])
      in
      PCSP.Params.make ~dtenv:params.dtenv ~kind_map ~fenv:params.fenv
        ~sol_space:params.sol_space ~id
        ~sol_for_eliminated:params.sol_for_eliminated ~messenger delta
    in
    c |> ExtTerm.nnf_of
    |> ExtTerm.cnf_of delta Map.Poly.empty
    |> Set.Poly.map ~f:(fun (_, _, phi) ->
        let uni_senv, _, phi =
          LogicOld.Formula.skolemize ~uni_senv:Map.Poly.empty ~use_fn_pred:false
            ~only_impure:true
          @@ ExtTerm.to_old_fml delta Map.Poly.empty phi
        in
        ExtTerm.of_old (uni_senv, phi))
    |> Set.union @@ PCSP.Problem.formulas_of pcsp
    |> PCSP.Problem.of_formulas ~params

  (* The moves of other predicates -- [(r, true)] grows [r], [(r, false)]
     shrinks it -- that an improvement of [pvar] may need and that the paper's
     improvement notion permits, so that fixing those predicates at [theta], as
     [check_optimality] does, may forbid an improvement that exists.  An
     improvement grows a maximized [pvar] and shrinks a minimized one.  Growing
     [r] may violate a clause with [r] in its body, shrinking [r] one with [r]
     in its head; the clause is repaired by growing a predicate of its head or
     shrinking one of its body, and those moves propagate in turn.  A move is
     counted and followed unless
     - it moves [pvar] itself or a predicate already certified optimal (a
       monotone extension cannot move that without contradicting its
       certificate);
     - it moves another target in its worse direction: "not worse" lets a
       maximized target only grow and a minimized one only shrink, while a
       non-target may move either way;
     - it is impossible: growing [r] with [theta r = true], shrinking [r] with
       [theta r = false], growing [r] with [theta r = false] beside a clause
       [r(x1, ..., xn) => false] (any growth is a violation: the [fail]/[query]
       predicate of Datalog-style inputs), or shrinking [r] with
       [theta r = true] beside a fact [r(x1, ..., xn)] -- both over distinct
       variables, since [r(0) => false] forbids growth at [0] only.
     The certificate is exact when nothing is counted.  Following only growth
     into clause heads is the maximized case alone: for a minimized target it
     counts nothing, and a certificate that had fixed a shrinkable body
     predicate of the target's defining clause was taken for exact although a
     strictly smaller target existed.  [targets] are the optimization targets,
     each maximized when [NonOptChecker.is_dup] holds of it. *)
  let improvement_moves pvar ~targets pcsp theta improved =
    let cls = Set.to_list @@ PCSP.Problem.clauses_of pcsp in
    let pvs_of = Set.Poly.map ~f:(ExtTerm.let_var_app >> fst) in
    let theta_is f r =
      match Map.Poly.find theta r with
      | Some t -> f @@ snd @@ ExtTerm.let_lam t
      | None -> false
    in
    let lone_atom_on_distinct_vars r atms =
      match Set.to_list atms with
      | [ atm ] -> (
          let r', args = ExtTerm.let_var_app atm in
          Stdlib.(r' = r)
          &&
          match
            Option.all
            @@ List.map args ~f:(fun t ->
                if ExtTerm.is_var t then Some (fst @@ ExtTerm.let_var t)
                else None)
          with
          | Some vs -> not (List.contains_dup ~compare:Stdlib.compare vs)
          | None -> false)
      | _ -> false
    in
    let impossible (r, grow) =
      if grow then
        theta_is ExtTerm.is_true r
        || theta_is ExtTerm.is_false r
           && List.exists cls ~f:(fun (_, ps, ns, phi) ->
               Set.is_empty ps && ExtTerm.is_false phi
               && lone_atom_on_distinct_vars r ns)
      else
        theta_is ExtTerm.is_false r
        || theta_is ExtTerm.is_true r
           && List.exists cls ~f:(fun (_, ps, ns, phi) ->
               Set.is_empty ns && ExtTerm.is_false phi
               && lone_atom_on_distinct_vars r ps)
    in
    let counted ((r, grow) as move) =
      Stdlib.(r <> pvar)
      && (not (Set.mem improved r))
      && ((not (List.mem targets r ~equal:Stdlib.( = )))
         || Bool.equal grow (NonOptChecker.is_dup r))
      && not (impossible move)
    in
    let successors (r, grow) =
      List.concat_map cls ~f:(fun (_, ps, ns, _) ->
          let ps = pvs_of ps and ns = pvs_of ns in
          if Set.mem (if grow then ns else ps) r then
            List.map (Set.to_list ps) ~f:(fun q -> (q, true))
            @ List.map (Set.to_list ns) ~f:(fun q -> (q, false))
          else [])
      |> List.filter ~f:counted
    in
    let rec go found = function
      | [] -> found
      | move :: todo ->
          let next =
            List.dedup_and_sort ~compare:Stdlib.compare
            @@ List.filter (successors move) ~f:(Fn.non (Set.mem found))
          in
          go (Set.union found (Set.Poly.of_list next)) (next @ todo)
    in
    go Set.Poly.empty [ (pvar, NonOptChecker.is_dup pvar) ]

  let check_optimality ?(only_simple = false) ~targets (messenger, id) improved
      pcsp delta theta priority pvar =
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
    (* Substituting [theta] for the other predicates keeps the termination
       problem small, and the certificate it yields — no better [pvar] leaves
       the other predicates as they are — is the paper's IsOpt (others not
       worse than [theta]) exactly when improving [pvar] can need no permitted
       move of another predicate ([improvement_moves]).  Otherwise the
       substitution turns a needed move into a violation and may certify a
       non-optimal solution; the caller then confirms the certificate with the
       improver before accepting it. *)
    let exact =
      only_simple
      || (not config.exact_opt_check)
      || Set.is_empty (improvement_moves pvar ~targets pcsp theta improved)
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
    (res, exact)

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
      ExtTerm.to_old_fml (Map.force_merge delta nepvs) Map.Poly.empty c
    in
    let bpvs =
      Map.Poly.keys nepvs @ full_priority
      |> Set.Poly.of_list
      |> Set.filter ~f:(Fn.non @@ Set.mem improved)
    in
    Debug.print_log ~tag:"improve"
    @@ lazy (sprintf "a pnCSP generated: %s" @@ LogicOld.Formula.str_of phi);
    let pcsp' =
      let constraint_ = ExtTerm.of_old_formula @@ Evaluator.simplify phi in
      let delta, constraint_ =
        if config.fix_improved_solutions then
          let fixed = Map.Poly.filter_keys theta ~f:(Set.mem improved) in
          ( Map.Poly.filter_keys delta ~f:(Fn.non @@ Set.mem improved),
            PCSP.Problem.subst_formula fixed constraint_ )
        else (delta, constraint_)
      in
      extend_pcsp_with (messenger, id) pcsp delta constraint_ nepvs
    in
    let pcsp' =
      let maxcs =
        (*ToDo: necessary?*)
        if config.fix_improved_solutions then Set.Poly.empty
        else
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
            if config.fix_improved_solutions then
              Map.Poly.fold theta ~init:theta'
                ~f:(fun ~key ~data acc ->
                  if Set.mem improved key then Map.Poly.set acc ~key ~data
                  else acc)
            else theta'
          in
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
      check_optimality ~only_simple:true ~targets:full_priority (None, Some 0)
        improved pcsp delta theta priority (List.hd_exn priority)
    with
    | (OptSat _ as sol), _ -> sol
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
                check_optimality ~targets:full_priority
                  (Some messenger, optimality_check_id)
                  improved pcsp delta theta priority (List.hd_exn priority)
              with
              | CHCOpt.Problem.Unknown, _ ->
                  (CHCOpt.Problem.Skip, false, optimality_check_id)
              | CHCOpt.Problem.OptSat sol, exact ->
                  (* an exact certificate settles the round; an inexact one is
                     only accepted once the improver has failed to improve the
                     same solution *)
                  if exact then
                    send_terminate optimality_check_id improve_task_id
                  else
                    Debug.print_log
                    @@ lazy
                         "[parallel_check_opt] inexact optimality certificate; \
                          waiting for the improver";
                  (CHCOpt.Problem.OptSat sol, exact, optimality_check_id)
              | _ -> failwith "only OptSat and Unknown are reachable"
              | exception Common.Messenger.Terminated ->
                  Debug.print_log @@ lazy "optimality_check_task terminated";
                  (CHCOpt.Problem.Skip, false, optimality_check_id)
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
              | CHCOpt.Problem.Unknown ->
                  (CHCOpt.Problem.Skip, true, improve_task_id)
              | sol (* only OptSat, OptSatInSpace, and Sat are reachable *) ->
                  send_terminate improve_task_id optimality_check_id;
                  (sol, true, improve_task_id)
              | exception Common.Messenger.Terminated ->
                  Debug.print_log @@ lazy "improve_task terminated";
                  (CHCOpt.Problem.Skip, true, improve_task_id)
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
          | Skip, _, id ->
              Debug.print_log
              @@ lazy
                   "One task finished with a useless result. Wait for the \
                    other task to complete.";
              let sol, _, _ = wait_other_task id in
              sol
          | (OptSat _ as sol), false, id when Stdlib.(id = optimality_check_id)
            -> (
              (* inexact certificate: the improver gets
                 [config.inexact_certificate_wait_ms] milliseconds to refute it (it
                 cannot be expected to prove Unsat quickly) *)
              ignore
              @@ Task.async task_pool (fun () ->
                  ignore
                  @@ Core_unix.nanosleep
                       (float_of_int config.inexact_certificate_wait_ms /. 1000.);
                  send_terminate optimality_check_id improve_task_id);
              match wait_other_task id with
              | (Sat _ as sol'), _, _ ->
                  Debug.print_log
                  @@ lazy
                       "[parallel_check_opt] the improver refuted an inexact \
                        optimality certificate";
                  sol'
              | (OptSat _ | OptSatInSpace _), _, _ -> sol
              | _ ->
                  Debug.print_log
                  @@ lazy
                       "[parallel_check_opt] accepting an inexact optimality \
                        certificate: the improver could not decide";
                  sol)
          | sol, _, id ->
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
      check_optimality ~only_simple:true ~targets:full_priority
        (None, PCSP.Params.new_id ())
        improved pcsp delta theta priority (List.hd_exn priority)
    with
    | CHCOpt.Problem.OptSat sol, _ -> CHCOpt.Problem.OptSat sol
    | _ -> (
        if !num_improved < improve_until then
          improve (None, Some 0) improved full_priority priority pcsp delta
            theta
        else
          match
            check_optimality ~targets:full_priority
              (None, PCSP.Params.new_id ())
              improved pcsp delta theta priority (List.hd_exn priority)
          with
          | OptSat sol, true -> OptSat sol
          | (OptSat _ as sol), false -> (
              match
                improve (None, Some 0) improved full_priority priority pcsp
                  delta theta
              with
              | Sat _ as sol' -> sol'
              | (OptSat _ | OptSatInSpace _) as sol' -> sol'
              | _ -> sol)
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
         (* [theta] may still interpret a predicate preprocessing removed
            from [delta]; [CandSol.of_subst] looks every key up in [delta],
            so unfiltered this trace line raised and only verbose runs
            crashed *)
         @@ CandSol.of_subst delta
         @@ CHCOpt.Problem.filter_sol delta theta);
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
        (Config.is_non_trival_mode config.side_conditions
        || Config.is_non_vacuous_mode config.side_conditions)
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
        if Config.is_non_trival_mode config.side_conditions then ([], Set.Poly.empty)
        else
          PCSP.Problem.clauses_of @@ pcsp
          |> Set.filter ~f:(fun (_, ps, ns, _) ->
              Fn.non Set.is_empty ps && Fn.non Set.is_empty ns)
          |> Set.to_list
          |> List.filter_mapi ~f:(fun i (param_senv, _, ns, phi) ->
              let pvs = Set.to_list @@ Set.Poly.map ns ~f:ExtTerm.let_var_app in
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
                  phi :: Set.to_list ns |> ExtTerm.and_of |> ExtTerm.fvs_of
                  |> Set.filter ~f:(Map.Poly.mem param_senv)
                  |> Set.Poly.map ~f:ExtTerm.mk_var
                  |> Set.to_list
                  |> List.sort ~compare:Stdlib.compare
                in
                let sargs =
                  List.map tvs
                    ~f:(ExtTerm.let_var >> fst >> Map.Poly.find_exn param_senv)
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
      let kind_map = Map.Poly.map nesenv ~f:(fun _ -> Kind.Tot []) in
      let params = PCSP.Problem.params_of pcsp in
      let params =
        {
          params with
          (* [force_merge] compares colliding values with [Stdlib.( = )], and a
             [Kind.t] can be [NWF]/[Parity], which carry a closure and a
             [Hashtbl]: a collision on such a key raises [Invalid_argument] from
             the comparison rather than the intended [failwith "force_merge"]
             (polymorphic comparison cannot handle either).  The keys added
             here are the freshly made
             non-empty predicates, so a collision is not expected; if one happens the
             message will be misleading. *)
          kind_map = Map.force_merge params.kind_map kind_map;
          senv = Map.force_merge params.senv nesenv;
        }
      in
      Set.Poly.union_list [ neclause1; neclause2; PCSP.Problem.clauses_of pcsp ]
      |> PCSP.Problem.of_clauses ~params
      |> PCSP.Problem.formulas_of
      |> PCSP.Problem.of_formulas ~params

  exception Missing_optimization_target of string * Ident.tvar
  exception Trivially_infeasible

  let require_targets ~stage targets environment =
    List.iter targets ~f:(fun target ->
        if not (Map.Poly.mem environment target) then
          raise (Missing_optimization_target (stage, target)))

  let optimize_checked ?(filename = None) full_priority pcsp =
    let check_problem_targets stage pcsp =
      (* A false clause proves infeasibility independently of the objectives;
         it must not become unknown just because their signatures vanished. *)
      if
        Set.exists (PCSP.Problem.formulas_of pcsp) ~f:(fun (_, phi) ->
            BoolTerm.is_false phi)
      then raise Trivially_infeasible;
      require_targets ~stage full_priority (PCSP.Problem.senv_of pcsp)
    in
    check_problem_targets "original signature" pcsp;
    let retain_targets pcsp =
      check_problem_targets "preprocessed signature" pcsp;
      pcsp
    in
    Debug.print_log ~tag:"optimization priority"
    @@ lazy (String.concat_map_list ~sep:"," full_priority ~f:name_of_tvar);
    let src_pcsp_wo_side_conds =
      pcsp |> preprocessor full_priority |> retain_targets
      |> PCSP.Problem.merge_clauses |> preprocessor full_priority
      |> retain_targets |> remove_unused_params
    in
    let src_pcsp =
      src_pcsp_wo_side_conds
      |> add_side_conditions full_priority
      |> preprocessor full_priority |> retain_targets |> remove_unused_params
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
            | Error err ->
                (* the configuration asks for a seed solution beside the
                   input, read from the working directory; without it there is
                   nothing to start from, which is a refusal of the run, not
                   an internal error *)
                Common.Refusal.refuse
                  "load_init_sol is set, so the initial solution is read from \
                   %s, which cannot be read: %s"
                  filename (Error.to_string_hum err))
        else None
      in
      match sol_opt with
      | None -> Solver.solve ~bpvs:(Set.Poly.of_list full_priority) src_pcsp
      | Some sol ->
          (* A loaded seed is a CANDIDATE, not an answer: it was taken as [Sat]
             without being checked against the constraints, and everything after
             this reasons about improving a solution it assumes is feasible.  The
             all-true predicate is the case that makes that fatal -- nothing can
             enlarge it, so it passes the optimality reasoning unchanged and is
             reported as the maximum, while violating the problem.  A stale .sol
             file from another run is enough: the file is looked up by the input's
             basename in the working directory.
             So the seed is checked here, the same way the answer would be: every
             constraint with the solution substituted must be valid.  A seed that
             fails is not an error in the problem, so the run continues by solving
             for an initial solution as it would have without one. *)
          let feasible =
            let senv = PCSP.Problem.senv_of src_pcsp in
            Set.for_all (PCSP.Problem.formulas_of src_pcsp)
              ~f:(fun (uni_senv, phi) ->
                let phi' = Term.subst sol phi in
                (not (Set.exists (ExtTerm.fvs_of phi') ~f:(Map.Poly.mem senv)))
                &&
                  try
                    Z3Smt.Z3interface.is_valid ~id:None (LogicOld.get_fenv ())
                    @@ ExtTerm.to_old_fml Map.Poly.empty uni_senv phi'
                  with exn_ when not (Common.Timer.is_async exn_) -> false)
          in
          if feasible then Ok (PCSP.Problem.Sat sol, 0 (*dummy*))
          else (
            Debug.print_log
            @@ lazy
                 "the loaded initial solution does not satisfy the \
                  constraints; solving for one instead";
            Solver.solve ~bpvs:(Set.Poly.of_list full_priority) src_pcsp)
    in
    match init_sol with
    | Ok (PCSP.Problem.Unsat _, _) -> (CHCOpt.Problem.Unsat, 0)
    | Ok (PCSP.Problem.Unknown, _) -> (CHCOpt.Problem.Unknown, 0)
    | Ok (PCSP.Problem.OutSpace _, _) -> (CHCOpt.Problem.Unknown, 0 (*ToDo*))
    | Ok (PCSP.Problem.Timeout, _) -> (CHCOpt.Problem.Timeout, 0)
    | Ok (PCSP.Problem.Sat theta, _) ->
        require_targets ~stage:"initial solution" full_priority theta;
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
                | Timeout, iter -> (Timeout, iter)
                | OptSat theta, iter | OptSatInSpace theta, iter ->
                    Debug.print_log
                      ~tag:
                        (sprintf "Optimization for (%s) is over"
                        @@ name_of_tvar p)
                    @@ lazy
                         (sprintf "The current candidate:\n%s"
                         @@ CandSol.str_of
                         @@ CandSol.of_subst delta
                         @@ CHCOpt.Problem.filter_sol delta theta);
                    Solver.reset ();
                    let improved = Set.add improved p in
                    (* [fix_improved_solutions]: the improved predicates'
                       solutions fixed in the problem for the rest; off, the
                       problem is unchanged *)
                    let pcsp =
                      if not config.fix_improved_solutions then pcsp
                      else
                        let fixed =
                          Map.Poly.filter_keys theta ~f:(Set.mem improved)
                        in
                        let pcsp = PCSP.Problem.subst ~elim:false fixed pcsp in
                        let params = PCSP.Problem.params_of pcsp in
                        (* Fixed predicates are definitions, not new unknowns.
                           Keep their recovery entries but remove their active
                           signatures; later improvement constraints substitute
                           these same values before extending the problem. *)
                        PCSP.Problem.update_params pcsp
                          {
                            params with
                            (* subst already materialized and substituted the
                               stable clauses into the raw formula set. *)
                            PCSP.Params.stable_clauses = Set.Poly.empty;
                            PCSP.Params.senv =
                              Map.Poly.filter_keys params.senv
                                ~f:(Fn.non @@ Set.mem improved);
                            kind_map =
                              Map.Poly.filter_keys params.kind_map
                                ~f:(Fn.non @@ Set.mem improved);
                          }
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

  let optimize ?filename full_priority pcsp =
    try optimize_checked ?filename full_priority pcsp with
    | Trivially_infeasible -> (CHCOpt.Problem.Unsat, 0)
    | Missing_optimization_target (stage, target) ->
        Debug.print_log
        @@ lazy
             (sprintf
                "optimization target %s is absent from %s; reported unknown"
                (name_of_tvar target) stage);
        (CHCOpt.Problem.Unknown, 0)
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
