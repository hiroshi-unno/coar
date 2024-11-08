open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open MuCLP.Problem
open Preprocessing

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  module Reducer = MuCLP.Reducer.Make ((
    struct
      let config =
        MuCLP.Reducer.Config.{ verbose = config.verbose; use_dwf = false }
    end :
      MuCLP.Reducer.Config.ConfigType))

  module Qelim = MuCLP.Qelim.Make (struct
    let config = config.qelim
  end)

  let pcsp_solver ~primal (* ToDo *) =
    let open Or_error in
    ExtFile.unwrap
      (if primal then config.pcsp_solver_primal else config.pcsp_solver_dual)
    >>= fun cfg ->
    PCSPSolver.Solver.(
      Ok
        (module Make (struct
          let config = cfg
        end) : SolverType))

  let optimizer_cfg = ExtFile.unwrap config.optimizer

  let preprocess ?(id = None) ?(elim_forall = true) ?(elim_exists = true)
      ?(elim_pvar_args = true) muclp =
    let open Or_error in
    optimizer_cfg >>= fun optimizer_cfg ->
    Ok (MuCLP.Optimizer.make optimizer_cfg)
    >>= fun (module Optimizer : MuCLP.Optimizer.OptimizerType) ->
    let muclp = if config.check_problem then check_problem muclp else muclp in
    Debug.print ~id @@ lazy (sprintf "before optimization: %s\n" @@ str_of muclp);
    let muclp =
      Optimizer.f ~id ~elim_forall ~elim_exists ~elim_pvar_args (simplify muclp)
    in
    Debug.print ~id @@ lazy (sprintf "after optimization: %s\n" @@ str_of muclp);
    Ok muclp

  let pfwcsp_of ?(id = None) ~messenger ~exc_info unknowns muclp =
    let muclp =
      let pvs = Kind.pred_sort_env_map_of unknowns in
      muclp |> aconv_tvar |> complete_tsort |> complete_psort pvs
    in
    (*Debug.print ~id @@ lazy (sprintf "Preprocessed muCLP: %s\n" @@ str_of muclp);*)
    let pfwcsp =
      let pfwcsp =
        let exchange = Option.is_some exc_info in
        Reducer.f ~id ~exchange ~messenger muclp unknowns
      in
      match exc_info with
      | None -> pfwcsp
      | Some (partial_sol_targets, dep_graph) ->
          PCSP.Problem.update_params pfwcsp
          @@ PCSP.Problem.
               { (params_of pfwcsp) with partial_sol_targets; dep_graph }
    in
    Debug.print ~id
    @@ lazy
         (sprintf "******* Generated pfwCSP:\n%s" @@ PCSP.Problem.str_of pfwcsp);
    pfwcsp

  let check ~primal ?(id = None) ~messenger ~exc_info muclp =
    let check_forall_only (exi_senv, kind_map) muclp :
        (solution * int) Or_error.t =
      let open Or_error.Monad_infix in
      pcsp_solver ~primal >>= fun (module PCSPSolver) ->
      muclp
      |> pfwcsp_of ~id ~messenger ~exc_info (exi_senv, kind_map)
      |> PCSP.Problem.map ~f:Logic.Term.refresh
      |> PCSPSolver.solve
      >>= function
      | PCSP.Problem.Sat _, num_iters -> Ok (Valid, num_iters)
      | Unsat _, num_iters -> Ok (Invalid, num_iters)
      | Unknown, num_iters -> Ok (Unknown, num_iters)
      | OutSpace _, _ -> failwith "out of space" (* TODO *)
      | Timeout, num_iters -> Ok (Timeout, num_iters)
    in
    let muclp, unknowns =
      let unknowns = (Map.Poly.empty, Map.Poly.empty) in
      if has_only_forall muclp then
        (* no encoding of existential quantifiers required *)
        (muclp, unknowns)
      else
        (* Skolemize existential quantifiers *)
        (*Debug.print ~id @@ lazy (sprintf "Input muCLP: %s\n" @@ str_of muclp);*)
        let muclp, unknowns = Qelim.elim_exists (muclp, unknowns) in
        Debug.print ~id @@ lazy (sprintf "Skolemized: %s\n" @@ str_of muclp);
        (muclp, unknowns)
    in
    check_forall_only unknowns muclp

  let rec solve_primal ?(id = None) ~messenger ~exc_info flip_on_failure muclp =
    Or_error.Monad_infix.(
      muclp |> check ~primal:true ~id ~messenger ~exc_info >>= function
      | ((Unknown | Timeout) as r), num_iters ->
          if flip_on_failure then
            solve_dual ~id ~messenger ~exc_info false muclp
          else Ok (r, num_iters)
      | x -> Ok x)

  and solve_dual ?(id = None) ~messenger ~exc_info flip_on_failure muclp =
    Or_error.Monad_infix.(
      get_dual muclp |> check ~primal:false ~id ~messenger ~exc_info
      >>= function
      | ((Unknown | Timeout) as r), num_iters ->
          if flip_on_failure then
            solve_primal ~id ~messenger ~exc_info false muclp
          else Ok (r, num_iters)
      | res, num_iters -> Ok (flip_solution res, num_iters))

  let solve_primal_dual muclp =
    let open Or_error.Monad_infix in
    assert (config.number_of_pairs >= 1);
    let pool =
      Util.Task.setup_pool ~num_additional_domains:(2 * config.number_of_pairs)
    in
    let rec gen_tasks i =
      if i < config.number_of_pairs then
        let id_primal = Some ((i * 2) + 1) in
        let id_dual = Some ((i * 2) + 2) in
        let task_primal =
          Util.Task.async pool (fun () ->
              Debug.print @@ lazy "task_prove";
              solve_primal ~id:id_primal ~messenger:None ~exc_info:None false
                muclp)
        in
        let task_dual =
          Util.Task.async pool (fun () ->
              Debug.print @@ lazy "task_disprove";
              solve_dual ~id:id_dual ~messenger:None ~exc_info:None false muclp)
        in
        task_primal :: task_dual :: gen_tasks (i + 1)
      else []
    in
    try
      gen_tasks 0 |> Util.Task.await_any_promise pool >>= function
      | sol, num_iters ->
          Debug.print @@ lazy "task over";
          Ok (sol, num_iters)
    with err -> Or_error.of_exn err

  (*type info += Examples of ExClauseSet.t
    let send_examples messenger id exs = send_boardcast messenger id @@ Examples exs
    let receive_examples messenger_opt id =
    match messenger_opt with
    | None -> Set.Poly.empty
    | Some messenger ->
      receive_all_infos_with messenger id ~filter:(function Examples _ -> true | _ -> false)
      |> List.map ~f:(function (_, Examples exs) -> exs | _ -> Set.Poly.empty)
      |> Set.Poly.union_list*)

  let receive_candidate_solutions messenger_opt mean_id cache =
    match messenger_opt with
    | None -> ()
    | Some messenger ->
        Messenger.receive_all_infos_with messenger mean_id ~filter:(function
          | PCSP.Problem.CandidateSolution _ -> true
          | _ -> false)
        |> List.iter ~f:(function
             | _, PCSP.Problem.CandidateSolution sol -> Hash_set.add cache sol
             | _ -> assert false)

  let send_records : (int option, int) Hashtbl.Poly.t = Hashtbl.Poly.create ()

  let send_partial_solutions messenger_from messenger_to main_id from_id to_id
      arity_map history cache =
    let target_pvars = Map.key_set arity_map in
    Hash_set.iter cache
      ~f:(fun (sol, sol_before_red, violated_clauses, full_clauses, lbs_opt) ->
        Debug.print
        @@ lazy
             (sprintf "*** A new candidate partial solution from [%d]:\n%s"
                (Option.value_exn from_id)
                (Logic.str_of_term_subst Logic.ExtTerm.str_of sol));
        let interm =
          let fast_checked =
            Map.Poly.filter_mapi sol ~f:(fun ~key ~data ->
                match Map.Poly.find arity_map key with
                | None -> None
                | Some (dep_pvars, arity) ->
                    let (uni_params, lambda_params), upper_bound =
                      let params =
                        List.mapi ~f:(fun i (_, s) ->
                            (Ident.Tvar (sprintf "x%d" (i + 1)), s))
                        @@ fst @@ Logic.ExtTerm.let_lam data
                      in
                      ( List.split_n params @@ (List.length params - arity),
                        Normalizer.normalize @@ Evaluator.simplify_neg
                        @@ Logic.ExtTerm.to_old_formula Map.Poly.empty
                             (Map.Poly.of_alist_exn params)
                             data
                        @@ List.map params ~f:(fst >> Logic.ExtTerm.mk_var) )
                    in
                    Debug.print
                    @@ lazy
                         (sprintf "*** fast partial solution checking for [%s]"
                         @@ Ident.name_of_tvar key);
                    if not (Hash_set.mem history (key, upper_bound)) then
                      (* ToDo: check if [is_qualified_partial_solution] is indeed sufficient for partial solution checking
                         [violated_clauses] may contain clauses that do not define [key] but such clauses will be ignored *)
                      if
                        not
                          (PCSP.Problem.is_qualified_partial_solution
                             ~print:Debug.print dep_pvars target_pvars
                             violated_clauses)
                      then (
                        Debug.print @@ lazy "no";
                        None)
                      else (
                        Debug.print @@ lazy "yes!";
                        Some (arity, (uni_params, lambda_params), upper_bound))
                    else (
                      Debug.print @@ lazy "yes!!";
                      Some (arity, (uni_params, lambda_params), upper_bound)))
          in
          Map.force_merge fast_checked
          @@
          match lbs_opt with
          | Some (senv, fenv, lbs) ->
              Debug.print
              @@ lazy "*** partial solution checking using lower bounds";
              let pvs =
                ClauseSet.partial_sols_of ~print:Debug.print
                  (Z3Smt.Z3interface.is_valid ~id:main_id fenv)
                  senv sol_before_red lbs full_clauses target_pvars
                  (Map.key_set fast_checked)
              in
              Map.Poly.filter_mapi sol ~f:(fun ~key ~data ->
                  if not @@ Set.mem pvs key then None
                  else
                    match Map.Poly.find arity_map key with
                    | None -> failwith "send_partial_solutions"
                    | Some (_dep_pvars, arity) ->
                        let (uni_params, lambda_params), upper_bound =
                          let params =
                            List.mapi ~f:(fun i (_, s) ->
                                (Ident.Tvar (sprintf "x%d" (i + 1)), s))
                            @@ fst @@ Logic.ExtTerm.let_lam data
                          in
                          ( List.split_n params @@ (List.length params - arity),
                            Normalizer.normalize @@ Evaluator.simplify_neg
                            @@ Logic.ExtTerm.to_old_formula Map.Poly.empty
                                 (Map.Poly.of_alist_exn params)
                                 data
                            @@ List.map params ~f:(fst >> Logic.ExtTerm.mk_var)
                          )
                        in
                        Some (arity, (uni_params, lambda_params), upper_bound))
          | None -> Map.Poly.empty
        in
        let bounds =
          Map.Poly.filter_mapi interm
            ~f:(fun
                ~key ~data:(arity, (uni_params, lambda_params), upper_bound) ->
              if Hash_set.mem history (key, upper_bound) then (
                Debug.print
                @@ lazy
                     (sprintf "the upper bound [%s] is not new"
                     @@ Formula.str_of
                     @@ Evaluator.simplify_neg upper_bound);
                None)
              else if
                Evaluator.is_valid
                  (Z3Smt.Z3interface.is_valid ~id:main_id @@ get_fenv ())
                  upper_bound
              then (
                Debug.print
                @@ lazy
                     (sprintf "the upper bound [%s] is trivial"
                     @@ Formula.str_of
                     @@ Evaluator.simplify_neg upper_bound);
                Hash_set.Poly.add history (key, upper_bound);
                None)
              else (
                Hash_set.Poly.add history (key, upper_bound);
                Debug.print
                @@ lazy
                     (sprintf "send %d -> %d : forall %s. %s (%s) => %s"
                        (Option.value_exn from_id) (Option.value_exn to_id)
                        (String.concat_map_list ~sep:"," uni_params
                           ~f:(fst >> Ident.name_of_tvar))
                        (Ident.name_of_tvar key)
                        (String.concat_map_list ~sep:"," lambda_params
                           ~f:(fst >> Ident.name_of_tvar))
                        (Formula.str_of upper_bound));
                let fresh_uni_params =
                  fst @@ refresh_sort_env_list uni_params
                in
                let sub =
                  Map.Poly.of_alist_exn
                  @@ List.map2_exn uni_params fresh_uni_params
                       ~f:(fun (v1, _) (v2, _) -> (v1, Logic.ExtTerm.mk_var v2))
                in
                let lb_pred =
                  ( Map.Poly.of_alist_exn @@ fresh_uni_params,
                    Logic.ExtTerm.mk_lambda lambda_params
                    @@ Logic.ExtTerm.subst sub @@ Logic.ExtTerm.of_old_formula
                    @@ Evaluator.simplify_neg upper_bound )
                in
                let ub_pred =
                  ( Map.Poly.of_alist_exn @@ fresh_uni_params,
                    Logic.ExtTerm.mk_lambda lambda_params
                    @@ Logic.ExtTerm.subst sub
                    @@ Logic.ExtTerm.of_old_formula upper_bound )
                in
                Hashtbl.Poly.update send_records from_id ~f:(function
                  | None -> 1
                  | Some times -> times + 1);
                Some (arity, lb_pred, ub_pred)))
        in
        if Fn.non Map.Poly.is_empty bounds then (
          (match messenger_to with
          | Some messenger_to ->
              Messenger.send_boardcast messenger_to main_id
              @@ PCSP.Problem.UpperBounds
                   (Map.Poly.map bounds ~f:(fun (ar, _, ub) -> (ar, ub)))
          | None -> ());
          match messenger_from with
          | Some messenger_from ->
              if config.send_lower_bounds then
                Messenger.send_boardcast messenger_from main_id
                @@ PCSP.Problem.LowerBounds
                     (Map.Poly.map bounds ~f:(fun (ar, lb, _) -> (ar, lb)))
              else ()
          | None -> ()));
    Hash_set.clear cache

  let id_mean = Some 0
  let id_primal = Some 1
  let id_dual = Some 2

  let solve_primal_dual_exc muclp =
    let open Or_error.Monad_infix in
    if config.number_of_pairs <> 1 then failwith "not supported";
    Hashtbl.Poly.set send_records ~key:id_primal ~data:0;
    Hashtbl.Poly.set send_records ~key:id_dual ~data:0;
    preprocess ~elim_forall:true ~elim_exists:true ~elim_pvar_args:true muclp
    >>= fun muclp ->
    let arity_map =
      let open Reducer.DepGraph in
      let g =
        transitive_closure @@ gen_init_graph (query_of muclp) @@ preds_of muclp
      in
      let reached_pvs pv =
        Set.Poly.map ~f:Ident.pvar_to_tvar
        @@ Set.add (Map.Poly.find_exn g pv).reachable pv
      in
      Debug.print @@ lazy ("dep_pvars_graph:\n" ^ Reducer.DepGraph.str_of g);
      Map.Poly.of_alist_exn
      @@ List.map (preds_of muclp) ~f:(fun (_, pv, params, _) ->
             (Ident.pvar_to_tvar pv, (reached_pvs pv, List.length params)))
    in
    let exc_info =
      if not config.gen_extra_partial_sols then
        Some (Map.Poly.empty, Map.Poly.empty)
      else
        Some
          ( Map.Poly.filter_mapi arity_map ~f:(fun ~key ~data:(_, arity) ->
                if arity = 0 then None
                else
                  Option.some @@ Set.Poly.singleton
                  @@ PCSP.Params.mk_random_info (Ident.uninterp key)
                       config.random_ex_bound config.random_ex_size),
            Map.Poly.map ~f:fst arity_map )
    in
    let arity_map = Map.change_keys arity_map ~f:Ident.uninterp in
    let messenger_primal = Some (Messenger.create 2) in
    let messenger_dual = Some (Messenger.create 2) in
    let pool = Util.Task.setup_pool ~num_additional_domains:2 in
    let task_primal =
      Util.Task.async pool (fun () ->
          muclp
          |> check ~primal:true ~id:id_primal ~messenger:messenger_primal
               ~exc_info)
    in
    let task_dual =
      Util.Task.async pool (fun () ->
          get_dual muclp
          |> check ~primal:false ~id:id_dual ~messenger:messenger_dual ~exc_info
          >>= function
          | res, num_iters -> Ok (flip_solution res, num_iters))
    in
    let sol_cache_primal = Hash_set.Poly.create () in
    let sol_cache_dual = Hash_set.Poly.create () in
    let send_history_primal = Hash_set.Poly.create () in
    let send_history_dual = Hash_set.Poly.create () in
    let rec inner () =
      match Atomic.get task_primal with
      | Some sol -> sol
      | None -> (
          match Atomic.get task_dual with
          | Some sol -> sol
          | None ->
              receive_candidate_solutions messenger_primal id_mean
                sol_cache_primal;
              receive_candidate_solutions messenger_dual id_mean sol_cache_dual;
              if
                Hash_set.is_empty sol_cache_primal
                && Hash_set.is_empty sol_cache_dual
              then ignore @@ Core_unix.nanosleep 0.1
              else (
                send_partial_solutions messenger_primal messenger_dual id_mean
                  id_primal id_dual arity_map send_history_primal
                  sol_cache_primal;
                send_partial_solutions messenger_dual messenger_primal id_mean
                  id_dual id_primal arity_map send_history_dual sol_cache_dual);
              inner ())
    in
    match inner () with Ok sol -> sol | Error err -> Or_error.of_exn err

  let resolve_auto muclp mode =
    if Stdlib.(mode = Config.Auto) then
      if has_only_forall muclp then (
        if has_only_nu muclp then
          Debug.print @@ lazy "vvvv muCLP shape: only forall-nu"
        else if has_only_mu muclp then
          Debug.print @@ lazy "vvvv muCLP shape: only forall-mu"
        else Debug.print @@ lazy "vvvv muCLP shape: only forall";
        Config.Prove)
      else if has_only_exists muclp then (
        if has_only_nu muclp then
          Debug.print @@ lazy "vvvv muCLP shape: only exists-nu"
        else if has_only_mu muclp then
          Debug.print @@ lazy "vvvv muCLP shape: only exists-mu"
        else Debug.print @@ lazy "vvvv muCLP shape: only exists";
        Config.Disprove)
      else (
        if has_only_nu muclp then
          Debug.print @@ lazy "vvvv muCLP shape: only nu"
        else if has_only_mu muclp then
          Debug.print @@ lazy "vvvv muCLP shape: only mu"
        else Debug.print @@ lazy "vvvv muCLP shape: otherwise";
        Config.Prove)
    else mode

  let solve ?(print_sol = false) muclp =
    let open Or_error.Monad_infix in
    Debug.print @@ lazy "======== MuVal ========";
    Hashtbl.Poly.clear send_records;
    (match resolve_auto muclp config.mode with
    | Config.Auto -> failwith "not reachable here"
    | Config.Prove ->
        Debug.print @@ lazy "-=-=-=-= proving -=-=-=-=";
        preprocess ~elim_forall:true ~elim_exists:true ~elim_pvar_args:true
          muclp
        >>= solve_primal ~messenger:None ~exc_info:None true
    | Config.Disprove ->
        Debug.print @@ lazy "-=-=-=-= disproving -=-=-=-=";
        preprocess ~elim_forall:true ~elim_exists:true ~elim_pvar_args:true
          muclp
        >>= solve_dual ~messenger:None ~exc_info:None true
    | Config.Parallel ->
        Debug.print @@ lazy "-=-=-=-= proving/disproving -=-=-=-=";
        Debug.set_id id_mean;
        preprocess ~id:id_mean ~elim_forall:true ~elim_exists:true
          ~elim_pvar_args:true muclp
        >>= solve_primal_dual
    | Config.ParallelExc ->
        Debug.print
        @@ lazy "-=-=-=-= proving/disproving exchange learned clauses -=-=-=-=";
        Debug.set_id id_mean;
        preprocess ~id:id_mean ~elim_forall:true ~elim_exists:true
          ~elim_pvar_args:true muclp
        >>= solve_primal_dual_exc)
    >>= function
    | sol, num_iters ->
        Debug.print @@ lazy "=========================";
        let info =
          match
            ( Hashtbl.Poly.find send_records id_primal,
              Hashtbl.Poly.find send_records id_dual )
          with
          | Some primal_num_sent, Some dual_num_sent ->
              sprintf "%d,%d|%d" num_iters primal_num_sent dual_num_sent
          | _ (*ToDo*) -> sprintf "%d" num_iters
        in
        if print_sol then
          print_endline
          @@
          if config.output_iteration then
            sprintf "%s,%s"
              ((if config.output_yes_no then lts_str_of_solution
                else str_of_solution)
                 sol)
              info
          else
            sprintf "%s"
              ((if config.output_yes_no then lts_str_of_solution
                else str_of_solution)
                 sol);
        Or_error.return (sol, num_iters, info)

  let solve_pcsp ?(print_sol = false) pcsp =
    let (module Preprocessor : Preprocessor.PreprocessorType) =
      Preprocessor.(make @@ Config.make true config.verbose 4 4 true)
    in
    Debug.print
    @@ lazy "************* converting pfwCSP to muCLP ***************";
    Preprocessor.solve
      (fun ?oracle pcsp ->
        ignore oracle;
        let open Or_error.Monad_infix in
        solve ~print_sol:false (of_chc pcsp) >>= fun (sol, num_iters, info) ->
        let sol =
          match sol with
          | Valid -> PCSP.Problem.Sat Map.Poly.empty (* ToDo *)
          | Invalid -> PCSP.Problem.Unsat None (* ToDo *)
          | Unknown -> PCSP.Problem.Unknown
          | Timeout -> PCSP.Problem.Timeout
        in
        if print_sol then
          print_endline
          @@
          if config.output_iteration then
            sprintf "%s,%s" (PCSP.Problem.str_of_solution sol) info
          else sprintf "%s" (PCSP.Problem.str_of_solution sol);
        Or_error.return (sol, { PCSatCommon.State.num_cegis_iters = num_iters }))
      pcsp

  let solve_interactive muclp =
    let pre_primal, muclp_primal =
      let bounds, phi, _ =
        if Formula.is_forall muclp.query then Formula.let_forall muclp.query
        else ([], muclp.query, Dummy)
      in
      let _, sorts, args, _ =
        try Atom.let_pvar_app @@ fst @@ Formula.let_atom phi
        with _ ->
          failwith @@ "unsupported shape of query: " ^ Formula.str_of phi
      in
      let senv = Map.Poly.of_alist_exn @@ Logic.(of_old_sort_env_list bounds) in
      let pre =
        Formula.mk_atom @@ Atom.mk_pvar_app (Ident.Pvar "PrePrimal") sorts args
      in
      ( (senv, pre),
        make muclp.preds @@ Formula.(forall bounds @@ mk_imply pre phi) )
    in
    let pre_dual, muclp_dual =
      let muclp = get_dual muclp in
      let bounds, phi, _ =
        if Formula.is_exists muclp.query then Formula.let_exists muclp.query
        else ([], muclp.query, Dummy)
      in
      let _, sorts, args, _ =
        Atom.let_pvar_app @@ fst @@ Formula.let_atom phi
      in
      let senv = Map.Poly.of_alist_exn @@ Logic.(of_old_sort_env_list bounds) in
      let pre =
        Formula.mk_atom @@ Atom.mk_pvar_app (Ident.Pvar "PreDual") sorts args
      in
      ( (senv, pre),
        make muclp.preds @@ Formula.(forall bounds @@ mk_imply pre phi) )
    in
    let ord_pvs_primal = Formula.pred_sort_env_of @@ snd pre_primal in
    let ord_pvs_dual = Formula.pred_sort_env_of @@ snd pre_dual in
    let pcsp_primal =
      let muclp_primal, unknowns =
        Qelim.elim_exists_in_preds
          (muclp_primal, (Map.Poly.empty, Map.Poly.empty))
      in
      PCSP.Problem.add_non_emptiness (Set.choose_exn ord_pvs_primal)
      @@ pfwcsp_of ~messenger:None ~exc_info:None
           (Kind.add_pred_env_set unknowns Kind.Ord ord_pvs_primal)
           muclp_primal
    in
    let pcsp_dual =
      let muclp_dual, unknowns =
        Qelim.elim_exists_in_preds (muclp_dual, (Map.Poly.empty, Map.Poly.empty))
      in
      PCSP.Problem.add_non_emptiness (Set.choose_exn ord_pvs_dual)
      @@ pfwcsp_of ~messenger:None ~exc_info:None
           (Kind.add_pred_env_set unknowns Kind.Ord ord_pvs_dual)
           muclp_dual
    in
    Debug.print
    @@ lazy
         (sprintf "pfwCSP for Primal Problem:\n%s\n"
         @@ PCSP.Problem.str_of pcsp_primal);
    Debug.print
    @@ lazy
         (sprintf "pfwCSP for Dual Problem:\n%s\n"
         @@ PCSP.Problem.str_of pcsp_dual);
    let open Or_error.Monad_infix in
    pcsp_solver ~primal:true
    (*ToDo:dual config is not used*) >>= fun (module PCSPSolver) ->
    Out_channel.output_string Out_channel.stdout "timeout in sec: ";
    Out_channel.flush Out_channel.stdout;
    let timeout =
      try Some (int_of_string @@ In_channel.input_line_exn In_channel.stdin)
      with _ -> None
    in
    let rec refine primal dual unknown pos neg =
      Out_channel.output_string Out_channel.stdout
        "action (primal/dual/unknown/pos/neg/end): ";
      Out_channel.flush Out_channel.stdout;
      match In_channel.input_line_exn In_channel.stdin with
      | "primal" -> (
          let phi =
            let pre = Logic.ExtTerm.of_old_formula @@ snd pre_primal in
            Logic.BoolTerm.and_of
              [
                Logic.BoolTerm.imply_of pre
                @@ Logic.ExtTerm.of_old_formula
                @@ Formula.mk_and unknown (Formula.mk_neg neg);
                Logic.BoolTerm.imply_of (Logic.ExtTerm.of_old_formula pos) pre;
              ]
          in
          let pcsp =
            PCSP.Problem.add_formula (fst pre_primal, phi) pcsp_primal
          in
          (match timeout with
          | None ->
              let bpvs =
                Set.Poly.map ord_pvs_primal ~f:(fst >> Ident.pvar_to_tvar)
              in
              PCSPSolver.solve ~bpvs pcsp
          | Some tm ->
              Timer.enable_timeout tm Fn.id ignore
                (fun () ->
                  let bpvs =
                    Set.Poly.map ord_pvs_primal ~f:(fst >> Ident.pvar_to_tvar)
                  in
                  PCSPSolver.solve ~bpvs pcsp)
                (fun _ res -> res)
                (fun _ -> function
                  | Timer.Timeout -> Or_error.return (PCSP.Problem.Timeout, -1)
                  | e -> raise e))
          >>= function
          | PCSP.Problem.Sat sol, _ ->
              (*Out_channel.print_endline @@ CandSol.str_of sol;*)
              let phi =
                Z3Smt.Z3interface.simplify (get_fenv ()) ~id:None
                @@ Evaluator.simplify
                @@ Logic.ExtTerm.to_old_fml Map.Poly.empty
                     ( fst pre_primal,
                       Logic.(
                         Term.subst sol @@ ExtTerm.of_old_formula
                         @@ snd pre_primal) )
              in
              let primal =
                Z3Smt.Z3interface.simplify ~id:None (get_fenv ())
                @@ Evaluator.simplify
                @@ Formula.or_of [ phi; primal ]
              in
              let unknown =
                Z3Smt.Z3interface.simplify ~id:None (get_fenv ())
                @@ Evaluator.simplify
                @@ Formula.and_of [ Formula.mk_neg phi; unknown ]
              in
              Out_channel.print_endline @@ Formula.str_of primal;
              if Z3Smt.Z3interface.is_sat ~id:None (get_fenv ()) unknown then
                refine primal dual unknown (Formula.mk_false ())
                  (Formula.mk_false ())
              else (
                Out_channel.print_endline "maximality is guaranteed";
                Or_error.return (Unknown, -1) (*Dummy*))
          | Unsat _, _ ->
              if Formula.is_false pos && Formula.is_false neg then (
                Out_channel.print_endline
                  "maximally weak precondition for dual property:";
                Out_channel.print_endline @@ Formula.str_of unknown;
                Or_error.return (Unknown, -1) (*Dummy*))
              else (
                Out_channel.print_endline
                  "the specified constraints for positive and negative \
                   examples are incorrect";
                refine primal dual unknown (Formula.mk_false ())
                  (Formula.mk_false ()))
          | (Unknown | Timeout), _ ->
              refine primal dual unknown (Formula.mk_false ())
                (Formula.mk_false ())
          | OutSpace _, _ -> assert false)
      | "dual" -> (
          let phi =
            let pre = Logic.ExtTerm.of_old_formula @@ snd pre_dual in
            Logic.BoolTerm.and_of
              [
                Logic.BoolTerm.imply_of pre
                @@ Logic.ExtTerm.of_old_formula
                @@ Formula.mk_and unknown (Formula.mk_neg neg);
                Logic.BoolTerm.imply_of (Logic.ExtTerm.of_old_formula pos) pre;
              ]
          in
          let pcsp = PCSP.Problem.add_formula (fst pre_dual, phi) pcsp_dual in
          (match timeout with
          | None ->
              let bpvs =
                Set.Poly.map ord_pvs_dual ~f:(fst >> Ident.pvar_to_tvar)
              in
              PCSPSolver.solve ~bpvs pcsp
          | Some tm ->
              Timer.enable_timeout tm Fn.id ignore
                (fun () ->
                  let bpvs =
                    Set.Poly.map ord_pvs_dual ~f:(fst >> Ident.pvar_to_tvar)
                  in
                  PCSPSolver.solve ~bpvs pcsp)
                (fun _ res -> res)
                (fun _ -> function
                  | Timer.Timeout -> Or_error.return (PCSP.Problem.Timeout, -1)
                  | e -> raise e))
          >>= function
          | PCSP.Problem.Sat sol, _ ->
              (*Out_channel.print_endline @@ Ast.CandSol.str_of sol;*)
              let phi =
                Z3Smt.Z3interface.simplify ~id:None (get_fenv ())
                @@ Evaluator.simplify
                @@ Logic.ExtTerm.to_old_fml Map.Poly.empty
                     ( fst pre_dual,
                       Logic.(
                         Term.subst sol @@ ExtTerm.of_old_formula
                         @@ snd pre_dual) )
              in
              let dual =
                Z3Smt.Z3interface.simplify ~id:None (get_fenv ())
                @@ Evaluator.simplify
                @@ Formula.or_of [ phi; dual ]
              in
              let unknown =
                Z3Smt.Z3interface.simplify ~id:None (get_fenv ())
                @@ Evaluator.simplify
                @@ Formula.and_of [ Formula.mk_neg phi; unknown ]
              in
              Out_channel.print_endline @@ Formula.str_of dual;
              if Z3Smt.Z3interface.is_sat ~id:None (get_fenv ()) unknown then
                refine primal dual unknown (Formula.mk_false ())
                  (Formula.mk_false ())
              else (
                Out_channel.print_endline "maximality is guaranteed";
                Or_error.return (Unknown, -1) (*Dummy*))
          | Unsat _, _ ->
              if Formula.is_false pos && Formula.is_false neg then (
                Out_channel.print_endline
                  "maximally weak precondition for primal property:";
                Out_channel.print_endline @@ Formula.str_of unknown;
                Or_error.return (Unknown, -1) (*Dummy*))
              else (
                Out_channel.print_endline
                  "the specified constraints for positive and negative \
                   examples are incorrect";
                refine primal dual unknown (Formula.mk_false ())
                  (Formula.mk_false ()))
          | (Unknown | Timeout), _ ->
              refine primal dual unknown (Formula.mk_false ())
                (Formula.mk_false ())
          | OutSpace _, _ -> assert false)
      | "pos" -> (
          Out_channel.output_string Out_channel.stdout "positive examples: ";
          Out_channel.flush Out_channel.stdout;
          match
            MuCLP.Parser.query_from_string ~print:Debug.print
            @@ In_channel.(input_line_exn stdin)
          with
          | Ok phi -> refine primal dual unknown (Formula.mk_or pos phi) neg
          | Error msg -> failwith (Error.to_string_hum msg))
      | "neg" -> (
          Out_channel.output_string Out_channel.stdout "negative examples: ";
          Out_channel.flush Out_channel.stdout;
          match
            MuCLP.Parser.query_from_string ~print:Debug.print
            @@ In_channel.(input_line_exn stdin)
          with
          | Ok phi -> refine primal dual unknown pos (Formula.mk_or neg phi)
          | Error msg -> failwith (Error.to_string_hum msg))
      | "unknown" ->
          Out_channel.print_endline @@ Formula.str_of unknown;
          refine primal dual unknown pos neg
      | "end" -> Or_error.return (Unknown, -1) (*Dummy*)
      | _ -> refine primal dual unknown pos neg
    in
    refine (Formula.mk_false ()) (Formula.mk_false ()) (Formula.mk_true ())
      (Formula.mk_false ()) (Formula.mk_false ())
end
