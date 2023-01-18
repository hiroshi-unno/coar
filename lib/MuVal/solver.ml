open Core
open Common
open Common.Ext
open Common.Util
open Ast
open Ast.LogicOld
open MuCLP.Problem

module Make (Cfg: Config.ConfigType) = struct
  let config = Cfg.config

  module Debug = Debug.Make (val Debug.Config.(if config.verbose then enable else disable))
  module Reducer = Reducer.Make (struct let config = config end)
  module Qelim = MuCLP.Qelim.Make (struct let config = config.qelim end)

  let pcsp_solver ()(* ToDo *) = let open Or_error in
    ExtFile.unwrap config.pcsp_solver >>= fun cfg ->
    Ok (module (PCSPSolver.Solver.Make (struct let config = cfg end)) : PCSPSolver.Solver.SolverType)

  let optimizer = let open Or_error in
    ExtFile.unwrap config.optimizer >>= fun cfg ->
    Ok (MuCLP.Optimizer.make cfg)

  let messenger = None
  let fenv = Map.Poly.empty (*TODO: generate fenv*)

  let preprocess muclp =
    Or_error.
      (optimizer >>= fun (module Optimizer : MuCLP.Optimizer.OptimizerType) ->
       let muclp = if config.check_problem then MuCLP.Problem.check_problem muclp else muclp in
       Debug.print @@ lazy (Printf.sprintf "Input muCLP: %s\n" @@ MuCLP.Problem.str_of muclp);
       let muclp = Optimizer.optimize @@ MuCLP.Problem.simplify muclp in
       Debug.print @@ lazy (Printf.sprintf "Simplified/Optimized muCLP: %s\n" @@ MuCLP.Problem.str_of muclp);
       Ok muclp)

  let pfwcsp_of ?(id=None) ~divide_query messenger gen_partial_info (ordpvs, fnpvs, fnsenv) muclp =
    let muclp =
      muclp |> MuCLP.Problem.aconv_tvar |> MuCLP.Problem.complete_tsort
      |> MuCLP.Problem.complete_psort (Map.of_set_exn @@ Set.Poly.union ordpvs fnpvs)
    in
    Debug.print @@ lazy (Printf.sprintf "Preprocessed muCLP: %s\n" @@ MuCLP.Problem.str_of muclp);
    let pcsp = Reducer.f ~id ~divide_query muclp messenger (ordpvs, fnpvs, fnsenv) in
    let params =
      { (PCSP.Problem.params_of pcsp) with
        PCSP.Params.partial_sol_targets = fst gen_partial_info;
        PCSP.Params.dep_graph = snd gen_partial_info }
    in
    let pfwcsp = PCSP.Problem.update_params pcsp params in
    Debug.print @@ lazy (Printf.sprintf "******* Generated pfwCSP:\n%s" @@ PCSP.Problem.str_of pfwcsp);
    pfwcsp

  let check_forall_only ~id ~divide_query messenger gen_partial_info (fnpvs, fnsenv) muclp : (solution * int) Or_error.t =
    Or_error.Monad_infix.
      (pcsp_solver () >>= fun (module PCSPSolver) ->
       pfwcsp_of ~id ~divide_query messenger gen_partial_info (Set.Poly.empty, fnpvs, fnsenv) muclp
       |> PCSP.Problem.map_if_raw ~f:(Set.Poly.map ~f:Logic.Term.refresh)
       |> PCSPSolver.solve >>= (function
           | PCSP.Problem.Sat _, num_iters -> Ok (Valid, num_iters)
           | Unsat, num_iters -> Ok (Invalid, num_iters)
           | Unknown, num_iters -> Ok (Unknown, num_iters)
           | OutSpace _, _ -> failwith "out of space" (* TODO *)))
  let check ?(id=None) ?(gen_partial_info=Map.Poly.empty, Map.Poly.empty) messenger muclp  =
    if MuCLP.Problem.has_only_forall muclp then begin
      (** no encoding of existential quantifiers required *)
      check_forall_only ~id messenger gen_partial_info (Set.Poly.empty, Map.Poly.empty) muclp
    end else begin
      Debug.print @@ lazy (Printf.sprintf "original: %s\n" @@ MuCLP.Problem.str_of muclp);
      let muclp, kindmap = Qelim.elim_exists muclp Set.Poly.empty in
      Debug.print @@ lazy (Printf.sprintf "existential quantifiers eliminated: %s\n" @@ MuCLP.Problem.str_of muclp);
      check_forall_only ~id messenger gen_partial_info kindmap muclp
    end

  let rec solve_primal
      ?(id=None) ?(gen_partial_info=Map.Poly.empty, Map.Poly.empty) ~divide_query messenger
      flip_on_failure muclp =
    Or_error.Monad_infix.
      (check ~id ~gen_partial_info ~divide_query messenger muclp
       >>= (function
           | Unknown, num_iters ->
             if flip_on_failure
             then solve_dual ~id ~gen_partial_info ~divide_query messenger false muclp
             else Ok (Unknown, num_iters)
           | x -> Ok x))
  and solve_dual
      ?(id=None) ?(gen_partial_info=Map.Poly.empty, Map.Poly.empty) ~divide_query messenger
      flip_on_failure muclp =
    Or_error.Monad_infix.
      (check ~id ~gen_partial_info ~divide_query messenger @@ MuCLP.Problem.get_dual muclp
       >>= (function
           | Unknown, num_iters ->
             if flip_on_failure
             then solve_primal ~id ~gen_partial_info ~divide_query messenger false muclp
             else Ok (Unknown, num_iters)
           | (res, num_iters) -> Ok (flip_solution res, num_iters)))

  let get_candidate_solution_messages messenger mean_id cache =
    match messenger with
    | Some messenger ->
      Messenger.receive_all_infos_with messenger mean_id ~filter:(function
          | PCSP.Problem.CandidateSolution _ -> true | _ -> false)
      |> List.iter ~f:(function
          | (_, PCSP.Problem.CandidateSolution sol) -> Hash_set.add cache sol
          | _ -> assert false)
    | None -> ()
  let send_records : (int option, int) Hashtbl.Poly.t = Hashtbl.Poly.create ()
  let send_partial_solutions messenger_from messenger_to main_id from_id to_id arity_map target_pvars history cache =
    Hash_set.iter cache ~f:(fun (sol, sol_before_red, violated_clauses, full_clauses, lbs_opt) ->
        Debug.print @@ lazy (sprintf "*** load a new candidate partial solution from: [%d]" @@ Option.value_exn from_id);
        let interm =
          let fast_checked =
            Map.Poly.filter_mapi sol ~f:(fun ~key ~data ->
                match Map.Poly.find arity_map key with
                | None -> None
                | Some (deq_pvars, arity) ->
                  let (uni_params, lambda_params), upper_bound =
                    let params =
                      List.mapi ~f:(fun i (_, s) -> Ident.Tvar (sprintf "x%d" (i + 1)), s) @@
                      fst @@ Logic.ExtTerm.let_lam data
                    in
                    List.split_n params @@ List.length params - arity,
                    Normalizer.normalize @@ Evaluator.simplify_neg @@
                    Logic.ExtTerm.to_old_formula Map.Poly.empty (Map.Poly.of_alist_exn params)
                      data (List.map params ~f:(fun (v, _) -> Logic.ExtTerm.mk_var v))
                  in
                  Debug.print @@ lazy (sprintf "*** fast partial solution checking for [%s]" @@ Ident.name_of_tvar key);
                  if not (Hash_set.mem history (key, upper_bound)) &&
                     (* ToDo: check if [is_qualified_partial_solution] is indeed sufficient for partial solution checking
                        [violated_clauses] may contain clauses that do not define [key] but such clauses will be ignored *)
                     not (PCSP.Problem.is_qualified_partial_solution
                            deq_pvars target_pvars violated_clauses) then begin
                    Debug.print @@ lazy "no";
                    None
                  end else begin
                    Debug.print @@ lazy "yes";
                    Some (arity, (uni_params, lambda_params), upper_bound)
                  end)
          in
          Map.force_merge fast_checked @@
          match lbs_opt with
          | Some (senv, fenv, lbs) ->
            Debug.print @@ lazy (sprintf "*** partial solution checking using lower bounds");
            let pvs =
              ClauseSet.partial_sols_of ~print:Debug.print (Z3Smt.Z3interface.is_valid ~id:main_id fenv)
                senv sol_before_red lbs full_clauses target_pvars (Map.key_set fast_checked)
            in
            Map.Poly.filter_mapi sol ~f:(fun ~key ~data ->
                if not @@ Set.Poly.mem pvs key then
                  None
                else
                  match Map.Poly.find arity_map key with
                  | None -> failwith "send_partial_solutions"
                  | Some (_deq_pvars, arity) ->
                    let (uni_params, lambda_params), upper_bound =
                      let params =
                        List.mapi ~f:(fun i (_, s) -> Ident.Tvar (sprintf "x%d" (i + 1)), s) @@
                        fst @@ Logic.ExtTerm.let_lam data
                      in
                      List.split_n params @@ List.length params - arity,
                      Normalizer.normalize @@ Evaluator.simplify_neg @@
                      Logic.ExtTerm.to_old_formula Map.Poly.empty (Map.Poly.of_alist_exn params)
                        data (List.map params ~f:(fun (v, _) -> Logic.ExtTerm.mk_var v))
                    in
                    Some (arity, (uni_params, lambda_params), upper_bound))
          | None -> Map.Poly.empty
        in
        let bounds =
          Map.Poly.filter_mapi interm ~f:(fun ~key ~data:(arity, (uni_params, lambda_params), upper_bound) ->
              if Hash_set.mem history (key, upper_bound) then begin
                Debug.print @@ lazy (sprintf "the partial solution [%s] has already been found" @@ Formula.str_of @@ Evaluator.simplify_neg upper_bound);
                None
              end else if Evaluator.is_valid
                  (Z3Smt.Z3interface.is_valid ~id:main_id @@ Atomic.get ref_fenv)
                  upper_bound
              then begin
                Debug.print @@ lazy (sprintf "the partial solution [%s] has no information" @@ Formula.str_of @@ Evaluator.simplify_neg upper_bound);
                Hash_set.Poly.add history (key, upper_bound);
                None
              end else begin
                Hash_set.Poly.add history (key, upper_bound);
                Debug.print @@ lazy
                  (sprintf "send %d -> %d : forall %s. %s (%s) => %s"
                     (Option.value_exn from_id)
                     (Option.value_exn to_id)
                     (String.concat_map_list ~sep:"," uni_params ~f:(fun (v, _) -> Ident.name_of_tvar v))
                     (Ident.name_of_tvar key)
                     (String.concat_map_list ~sep:"," lambda_params ~f:(fun (v, _) -> Ident.name_of_tvar v))
                     (Formula.str_of upper_bound));
                let fresh_uni_params = fst @@ refresh_sort_env_list uni_params in
                let sub =
                  Map.Poly.of_alist_exn @@ List.map2_exn uni_params fresh_uni_params
                    ~f:(fun (v1, _) (v2, _) -> v1, Logic.ExtTerm.mk_var v2)
                in
                let lb_pred =
                  Map.Poly.of_alist_exn @@ fresh_uni_params,
                  Logic.ExtTerm.mk_lambda lambda_params @@
                  Logic.ExtTerm.subst sub @@ Logic.ExtTerm.of_old_formula @@ Evaluator.simplify_neg upper_bound
                in
                let ub_pred =
                  Map.Poly.of_alist_exn @@ fresh_uni_params,
                  Logic.ExtTerm.mk_lambda lambda_params @@
                  Logic.ExtTerm.subst sub @@ Logic.ExtTerm.of_old_formula upper_bound
                in
                Hashtbl.Poly.update send_records from_id ~f:(function None -> 1 | Some times -> times + 1);
                Some (arity, lb_pred, ub_pred)
              end)
        in
        if Fn.non Map.Poly.is_empty bounds then begin
          (match messenger_to with
           | Some messenger_to ->
             Messenger.send_boardcast messenger_to main_id @@
             PCSP.Problem.UpperBounds (Map.Poly.map bounds ~f:(fun (ar, _lb, ub) -> ar, ub))
           | None -> ());
          (match messenger_from with
           | Some messenger_from ->
             Messenger.send_boardcast messenger_from main_id @@
             PCSP.Problem.LowerBounds (Map.Poly.map bounds ~f:(fun (ar, lb, _ub) -> ar, lb))
           | None -> ())
        end);
    Hash_set.clear cache

  let id_primal = Some 1
  let id_dual = Some 2
  let solve_primal_dual muclp = let open Or_error.Monad_infix in
    let messenger = None in
    let pool = Util.Task.setup_pool ~num_additional_domains:2 in
    let task_primal = Util.Task.async pool (fun () ->
        Debug.print @@ lazy "task_prove";
        solve_primal ~id:id_primal ~divide_query:false messenger false muclp) in
    let task_dual = Util.Task.async pool (fun () ->
        Debug.print @@ lazy "task_disprove";
        solve_dual ~id:id_dual ~divide_query:false messenger false muclp) in
    try Util.Task.await_any_promise pool [task_primal; task_dual] >>= function (sol, num_iters) ->
        Debug.print @@ lazy "task over";
        Ok (sol, num_iters)
    with err -> Or_error.of_exn err

  let solve_primal_dual_exc muclp = let open Or_error.Monad_infix in
    pcsp_solver () >>= fun (module PCSPSolver) ->
    let id_mean = Some 0 in
    Debug.set_id id_mean;
    Hashtbl.Poly.set send_records ~key:id_primal ~data:0;
    Hashtbl.Poly.set send_records ~key:id_dual ~data:0;
    preprocess muclp >>= fun muclp_primal ->
    let arity_map = let open Reducer.DepGraph in
      let g = transitive_closure @@
        gen_init_graph (MuCLP.Problem.query_of muclp_primal) (MuCLP.Problem.preds_of muclp_primal)
      in
      let reached_pvs pv =
        Set.Poly.map ~f:Ident.pvar_to_tvar @@
        Set.Poly.add (Map.Poly.find_exn g pv).reachable pv
      in
      Debug.print @@ lazy ("deppvar_graph:\n" ^ Reducer.DepGraph.str_of g);
      Map.Poly.of_alist_exn @@ List.map ~f:(fun (_, pv, params, _) ->
          Ident.pvar_to_tvar pv, (reached_pvs pv, List.length params)) @@
      MuCLP.Problem.preds_of muclp_primal
    in
    let target_pvars =
      Set.Poly.of_list @@ List.map ~f:(fun (_, pvar, _, _) -> Ident.pvar_to_tvar pvar) @@
      MuCLP.Problem.preds_of muclp_primal
    in
    Ok (MuCLP.Problem.get_dual muclp_primal) >>= fun muclp_dual ->
    let gen_partial_info =
      if not config.gen_extra_partial_sols then
        Map.Poly.empty, Map.Poly.empty
      else
        Map.Poly.filter_mapi arity_map ~f:(fun ~key ~data:(_, arity) ->
            if arity = 0 then None
            else
              let tvar = Ident.uninterp key in
              Option.some @@ Set.Poly.singleton @@
              PCSP.Params.mk_random_info tvar config.random_ex_bound config.random_ex_size),
        Map.Poly.map ~f:fst arity_map
    in
    let arity_map = Map.change_keys arity_map ~f:Ident.uninterp in
    let messenger_primal = Some (Messenger.create 2) in
    let messenger_dual = Some (Messenger.create 2) in
    let pool = Util.Task.setup_pool ~num_additional_domains:2 in
    let task_primal =
      Util.Task.async pool (fun () ->
          match check ~id:id_primal ~divide_query:true ~gen_partial_info messenger_primal muclp_primal with
          | Ok r -> Ok r
          | Error exn -> Error exn)
    in
    let task_dual =
      Util.Task.async pool (fun () ->
          match check ~id:id_dual ~divide_query:true ~gen_partial_info messenger_dual muclp_dual with
          | Ok (res, num_iters) -> Ok (flip_solution res, num_iters)
          | Error exn -> Error exn)
    in
    let sol_cache_primal = Hash_set.Poly.create () in
    let sol_cache_dual = Hash_set.Poly.create () in
    let send_history_primal = Hash_set.Poly.create () in
    let send_history_dual = Hash_set.Poly.create () in
    let rec inner () =
      match Atomic.get task_primal with
      | Some sol -> sol
      | None ->
        match Atomic.get task_dual with
        | Some sol -> sol
        | None ->
          get_candidate_solution_messages messenger_primal id_mean sol_cache_primal;
          get_candidate_solution_messages messenger_dual id_mean sol_cache_dual;
          if Hash_set.is_empty sol_cache_primal && Hash_set.is_empty sol_cache_dual then
            ignore @@ Core_unix.nanosleep 0.1
          else begin
            send_partial_solutions
              messenger_primal messenger_dual id_mean id_primal id_dual
              arity_map target_pvars send_history_primal sol_cache_primal;
            send_partial_solutions
              messenger_dual messenger_primal id_mean id_dual id_primal
              arity_map target_pvars send_history_dual sol_cache_dual
          end;
          inner ()
    in
    match inner () with Ok sol -> sol | Error err -> Or_error.of_exn err

  let resolve_auto muclp mode =
    if Stdlib.(mode = Config.Auto) then
      if MuCLP.Problem.has_only_forall muclp then begin
        (if MuCLP.Problem.has_only_nu muclp then
           Debug.print @@ lazy "vvvv muCLP shape: only forall-nu"
         else if MuCLP.Problem.has_only_mu muclp then
           Debug.print @@ lazy "vvvv muCLP shape: only forall-mu"
         else
           Debug.print @@ lazy "vvvv muCLP shape: only forall");
        Config.Prove
      end else if MuCLP.Problem.has_only_exists muclp then begin
        (if MuCLP.Problem.has_only_nu muclp then
           Debug.print @@ lazy "vvvv muCLP shape: only exists-nu"
         else if MuCLP.Problem.has_only_mu muclp then
           Debug.print @@ lazy "vvvv muCLP shape: only exists-mu"
         else
           Debug.print @@ lazy "vvvv muCLP shape: only exists");
        Config.Disprove
      end else begin
        (if MuCLP.Problem.has_only_nu muclp then
           Debug.print @@ lazy "vvvv muCLP shape: only nu"
         else if MuCLP.Problem.has_only_mu muclp then
           Debug.print @@ lazy "vvvv muCLP shape: only mu"
         else
           Debug.print @@ lazy "vvvv muCLP shape: otherwise");
        Config.Prove
      end
    else mode
  let solve ?(print_sol=false) muclp = let open Or_error.Monad_infix in
    Debug.print @@ lazy "======== MuVal ========";
    Hashtbl.Poly.clear send_records;
    preprocess muclp >>= fun muclp ->
    begin match resolve_auto muclp config.mode with
      | Config.Auto -> failwith "not reachable here"
      | Config.Prove ->
        Debug.print @@ lazy "-=-=-=-= proving -=-=-=-=";
        solve_primal ~id:(Some 0) ~divide_query:false messenger true muclp
      | Config.Disprove ->
        Debug.print @@ lazy "-=-=-=-= disproving -=-=-=-=";
        solve_dual ~id:(Some 0) ~divide_query:false messenger true muclp
      | Config.Parallel ->
        Debug.print @@ lazy "-=-=-=-= proving/disproving -=-=-=-=";
        solve_primal_dual muclp
      | Config.ParallelExc ->
        Debug.print @@ lazy "-=-=-=-= proving/disproving exchange learned clauses -=-=-=-=";
        solve_primal_dual_exc muclp
    end >>= (function (sol, num_iters) ->
        Debug.print @@ lazy "=========================";
        let primal_time = Hashtbl.Poly.find_or_add ~default:(fun _ -> -1) send_records id_primal in
        let dual_time = Hashtbl.Poly.find_or_add ~default:(fun _ -> -1) send_records id_dual in
        let info =
          if primal_time >= 0 && dual_time >= 0 then
            sprintf "%d,%d|%d" num_iters primal_time dual_time
          else sprintf "%d" num_iters
        in
        if print_sol then
          print_endline @@
          if config.output_iteration then
            Printf.sprintf "%s,%s" (MuCLP.Problem.str_of_solution sol) info
          else
            Printf.sprintf "%s" (MuCLP.Problem.str_of_solution sol);
        Or_error.return (sol, num_iters, info))

  let solve_pcsp ?(print_sol=false) pcsp =
    let pvar_eliminator =
      Ok (PCSat.PvarEliminator.make (PCSat.PvarEliminator.Config.make config.verbose 4 4 true))
    in
    let open Or_error.Monad_infix in
    pvar_eliminator >>= fun (module PvarEliminator : PCSat.PvarEliminator.PvarEliminatorType) ->
    Debug.print @@ lazy "************* converting pfwCSP to muCLP ***************";
    PvarEliminator.solve (fun ?oracle pcsp ->
        ignore oracle;
        solve ~print_sol:false (MuCLP.Problem.of_chc pcsp) >>= fun (solution, iteration, info) ->
        let solution =
          match solution with
          | MuCLP.Problem.Valid -> PCSP.Problem.Sat (Map.Poly.empty(* ToDo *))
          | MuCLP.Problem.Invalid -> PCSP.Problem.Unsat
          | MuCLP.Problem.Unknown -> PCSP.Problem.Unknown
        in
        if print_sol then print_endline @@
          if config.output_iteration then
            Printf.sprintf "%s,%s" (PCSP.Problem.str_of_solution solution) info
          else
            Printf.sprintf "%s" (PCSP.Problem.str_of_solution solution);
        Or_error.return (solution, { PCSatCommon.State.num_cegis_iters = iteration })) pcsp

  let solve_lts ?(print_sol=false) (lts, p) =
    Debug.print @@ lazy "************* converting LTS to muCLP ***************";
    Debug.print (lazy ("input LTS:\n" ^ LTS.Problem.str_of_lts lts));
    let lvs, cps, lts = LTS.Problem.analyze lts in
    Debug.print (lazy ("simplified LTS:\n" ^ LTS.Problem.str_of_lts lts));
    match p with
    | LTS.Problem.Term | LTS.Problem.NonTerm ->
      let open Or_error.Monad_infix in
      MuCLP.Problem.of_lts ~live_vars:(Some lvs) ~cut_points:(Some cps) (lts, p)
      |> solve ~print_sol:false >>= fun (solution, iteration, info) ->
      if print_sol then print_endline @@
        if config.output_iteration then
          Printf.sprintf "%s,%s" (MuCLP.Problem.lts_str_of_solution solution) info
        else
          Printf.sprintf "%s" @@ MuCLP.Problem.lts_str_of_solution solution;
      Or_error.return (solution, iteration)
    | LTS.Problem.CondTerm ->
      let muclp = MuCLP.Problem.of_lts ~live_vars:(Some lvs) ~cut_points:(Some cps) (lts, LTS.Problem.Term) in
      let pre_term, muclp_term =
        let bounds, phi, _ =
          if Formula.is_forall muclp.query then Formula.let_forall muclp.query
          else [], muclp.query, Dummy
        in
        let atm, _ = Formula.let_atom phi in
        let _, sorts, args, _ = Atom.let_pvar_app atm in
        let senv = Map.Poly.of_alist_exn @@ Logic.of_old_sort_env_list Logic.ExtTerm.of_old_sort bounds in
        let pre = Formula.mk_atom @@ Atom.mk_pvar_app (Ident.Pvar "PreTerm") sorts args in
        (senv, pre),
        MuCLP.Problem.make muclp.preds (Formula.forall bounds @@ Formula.mk_imply pre phi)
      in
      let pre_nonterm, muclp_nonterm =
        let muclp = MuCLP.Problem.get_dual muclp in
        let bounds, phi, _ =
          if Formula.is_exists muclp.query then Formula.let_exists muclp.query
          else [], muclp.query, Dummy in
        let atm, _ = Formula.let_atom phi in
        let _, sorts, args, _ = Atom.let_pvar_app atm in
        let senv = Map.Poly.of_alist_exn @@ Logic.of_old_sort_env_list Logic.ExtTerm.of_old_sort bounds in
        let pre = Formula.mk_atom @@ Atom.mk_pvar_app (Ident.Pvar "PreNonTerm") sorts args in
        (senv, pre),
        MuCLP.Problem.make muclp.preds (Formula.forall bounds @@ Formula.mk_imply pre phi)
      in
      let ord_pvs_term = Formula.pred_sort_env_of @@ snd pre_term in
      let ord_pvs_nonterm = Formula.pred_sort_env_of @@ snd pre_nonterm in
      let muclp_nonterm, (fnpvs, fnsenv) =
        Qelim.elim_exists_in_preds muclp_nonterm Set.Poly.empty
      in
      let pcsp_term =
        PCSP.Problem.add_non_emptiness (Set.Poly.choose_exn ord_pvs_term) @@
        pfwcsp_of ~divide_query:false  messenger (Map.Poly.empty, Map.Poly.empty) 
          (ord_pvs_term(* ToDo *), Set.Poly.empty, Map.Poly.empty) @@
        muclp_term
      in
      let pcsp_nonterm =
        PCSP.Problem.add_non_emptiness (Set.Poly.choose_exn ord_pvs_nonterm) @@
        pfwcsp_of ~divide_query:false messenger (Map.Poly.empty, Map.Poly.empty)
          (ord_pvs_nonterm(* ToDo *), fnpvs, fnsenv) @@
        muclp_nonterm
      in
      Debug.print @@ lazy (Printf.sprintf "pfwCSP for Termination:\n%s\n" @@ PCSP.Problem.str_of pcsp_term);
      Debug.print @@ lazy (Printf.sprintf "pfwCSP for Non-termination:\n%s\n" @@ PCSP.Problem.str_of pcsp_nonterm);
      let open Or_error.Monad_infix in
      pcsp_solver () >>= fun pcsp_solver ->
      let (module PCSPSolver) = pcsp_solver in
      Out_channel.output_string Out_channel.stdout "timeout in sec: ";
      Out_channel.flush Out_channel.stdout;
      let timeout = try Some (int_of_string @@ In_channel.input_line_exn In_channel.stdin) with _ -> None in
      let rec refine term nonterm unknown pos neg =
        Out_channel.output_string Out_channel.stdout "action (term/nonterm/unknown/pos/neg/end): ";
        Out_channel.flush Out_channel.stdout;
        match In_channel.input_line_exn In_channel.stdin with
        | "term" ->
          let phi =
            let pre = Logic.ExtTerm.of_old_formula @@ snd pre_term in
            Logic.BoolTerm.and_of
              [Logic.BoolTerm.imply_of pre (Logic.ExtTerm.of_old_formula (Formula.mk_and unknown (Formula.mk_neg neg)));
               Logic.BoolTerm.imply_of (Logic.ExtTerm.of_old_formula pos) pre] in
          let pcsp = PCSP.Problem.add_formula (fst pre_term, phi) pcsp_term in
          (match timeout with
           | None -> PCSPSolver.solve ~bpvs:(Set.Poly.map ~f:(fun (Ident.Pvar x, _) -> Ident.Tvar x) ord_pvs_term) pcsp
           | Some tm ->
             Timer.enable_timeout tm Fn.id ignore
               (fun () -> PCSPSolver.solve ~bpvs:(Set.Poly.map ~f:(fun (Ident.Pvar x, _) -> Ident.Tvar x) ord_pvs_term) pcsp)
               (fun _ res -> res)
               (fun _ -> function Timer.Timeout -> Or_error.return (PCSP.Problem.Unknown, -1) | e -> raise e))
          >>= (function
              | PCSP.Problem.Sat sol, _ ->
                (*Out_channel.print_endline @@ CandSol.str_of sol;*)
                let phi =
                  Z3Smt.Z3interface.simplify fenv ~id:None @@ Evaluator.simplify @@
                  Logic.ExtTerm.to_old_formula Map.Poly.empty (fst pre_term)
                    (Logic.Term.subst sol @@ Logic.ExtTerm.of_old_formula @@ snd pre_term) [] in
                let term = Z3Smt.Z3interface.simplify ~id:None fenv @@ Evaluator.simplify @@ Formula.or_of [phi; term] in
                let unknown = Z3Smt.Z3interface.simplify ~id:None fenv @@ Evaluator.simplify @@ Formula.and_of [Formula.mk_neg phi; unknown] in
                Out_channel.print_endline @@ Formula.str_of term;
                if Z3Smt.Z3interface.is_sat ~id:None fenv unknown then
                  refine term nonterm unknown (Formula.mk_false ()) (Formula.mk_false ())
                else begin
                  Out_channel.print_endline "maximality is guaranteed";
                  Or_error.return (Unknown, -1)(*Dummy*)
                end
              | Unsat, _ ->
                if Formula.is_false pos && Formula.is_false neg then begin
                  Out_channel.print_endline "maximally weak precondition for non-termination:";
                  Out_channel.print_endline @@ Formula.str_of unknown;
                  Or_error.return (Unknown, -1)(*Dummy*)
                end else begin
                  Out_channel.print_endline "the specified constraints for positive and negative examples are incorrect";
                  refine term nonterm unknown (Formula.mk_false ()) (Formula.mk_false ())
                end
              | Unknown, _ -> refine term nonterm unknown (Formula.mk_false ()) (Formula.mk_false ())
              | OutSpace _ , _ -> assert false)
        | "nonterm" ->
          let phi =
            let pre = Logic.ExtTerm.of_old_formula @@ snd pre_nonterm in
            Logic.BoolTerm.and_of
              [Logic.BoolTerm.imply_of pre (Logic.ExtTerm.of_old_formula (Formula.mk_and unknown (Formula.mk_neg neg)));
               Logic.BoolTerm.imply_of (Logic.ExtTerm.of_old_formula pos) pre] in
          let pcsp = PCSP.Problem.add_formula (fst pre_nonterm, phi) pcsp_nonterm in
          (match timeout with
           | None -> PCSPSolver.solve ~bpvs:(Set.Poly.map ~f:(fun (Ident.Pvar x, _) -> Ident.Tvar x) ord_pvs_nonterm) pcsp
           | Some tm ->
             Timer.enable_timeout tm Fn.id ignore
               (fun () -> PCSPSolver.solve ~bpvs:(Set.Poly.map ~f:(fun (Ident.Pvar x, _) -> Ident.Tvar x) ord_pvs_nonterm) pcsp)
               (fun _ res -> res)
               (fun _ -> function Timer.Timeout -> Or_error.return (PCSP.Problem.Unknown, -1) | e -> raise e))
          >>= (function
              | PCSP.Problem.Sat sol, _ ->
                (*Out_channel.print_endline @@ Ast.CandSol.str_of sol;*)
                let phi =
                  Z3Smt.Z3interface.simplify ~id:None fenv @@ Evaluator.simplify @@
                  Logic.ExtTerm.to_old_formula Map.Poly.empty (fst pre_nonterm)
                    (Logic.Term.subst sol @@ Logic.ExtTerm.of_old_formula @@ snd pre_nonterm) [] in
                let nonterm = Z3Smt.Z3interface.simplify ~id:None fenv @@ Evaluator.simplify @@ Formula.or_of [phi; nonterm] in
                let unknown = Z3Smt.Z3interface.simplify ~id:None fenv @@ Evaluator.simplify @@ Formula.and_of [Formula.mk_neg phi; unknown] in
                Out_channel.print_endline @@ Formula.str_of nonterm;
                if Z3Smt.Z3interface.is_sat ~id:None fenv unknown then
                  refine term nonterm unknown (Formula.mk_false ()) (Formula.mk_false ())
                else begin
                  Out_channel.print_endline "maximality is guaranteed";
                  Or_error.return (Unknown, -1)(*Dummy*)
                end
              | Unsat, _ ->
                if Formula.is_false pos && Formula.is_false neg then begin
                  Out_channel.print_endline "maximally weak precondition for termination:";
                  Out_channel.print_endline @@ Formula.str_of unknown;
                  Or_error.return (Unknown, -1)(*Dummy*)
                end else begin
                  Out_channel.print_endline "the specified constraints for positive and negative examples are incorrect";
                  refine term nonterm unknown (Formula.mk_false ()) (Formula.mk_false ())
                end
              | Unknown, _ -> refine term nonterm unknown (Formula.mk_false ()) (Formula.mk_false ())
              | OutSpace _, _ -> assert false)
        | "pos" ->
          Out_channel.output_string Out_channel.stdout "positive examples: ";
          Out_channel.flush Out_channel.stdout;
          (match MuCLP.Parser.formula_from_string @@ In_channel.input_line_exn In_channel.stdin with
           | Ok phi -> refine term nonterm unknown (Formula.mk_or pos phi) neg
           | Error msg -> failwith (Error.to_string_hum msg))
        | "neg" ->
          Out_channel.output_string Out_channel.stdout "negative examples: ";
          Out_channel.flush Out_channel.stdout;
          (match MuCLP.Parser.formula_from_string @@ In_channel.input_line_exn In_channel.stdin with
           | Ok phi -> refine term nonterm unknown pos (Formula.mk_or neg phi)
           | Error msg -> failwith (Error.to_string_hum msg))
        | "unknown" ->
          Out_channel.print_endline @@ Formula.str_of unknown;
          refine term nonterm unknown pos neg
        | "end" -> Or_error.return (Unknown, -1)(*Dummy*)
        | _ -> refine term nonterm unknown pos neg
      in
      refine (Formula.mk_false ()) (Formula.mk_false ()) (Formula.mk_true ()) (Formula.mk_false ()) (Formula.mk_false ())
    | LTS.Problem.Safe | LTS.Problem.NonSafe | LTS.Problem.MuCal | LTS.Problem.Rel -> assert false
end
