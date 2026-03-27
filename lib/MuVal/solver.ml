open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open Preprocessing

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  (** validity checking for muCLP *)

  module Reducer = MuCLP.Reducer.Make (
    struct
      let config =
        MuCLP.Reducer.Config.{ verbose = config.verbose; use_dwf = false }
    end :
      MuCLP.Reducer.Config.ConfigType)

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
    let muclp =
      if config.check_problem then MuCLP.Problem.check_problem muclp else muclp
    in
    Debug.print ~id
    @@ lazy (sprintf "before optimization: %s\n" @@ MuCLP.Problem.str_of muclp);
    let muclp =
      Optimizer.f ~id ~elim_forall ~elim_exists ~elim_pvar_args
        (MuCLP.Problem.simplify muclp)
    in
    Debug.print ~id
    @@ lazy (sprintf "after optimization: %s\n" @@ MuCLP.Problem.str_of muclp);
    Ok muclp

  let pfwcsp_of ?(id = None) ~messenger ~exc_info unknowns muclp =
    let muclp =
      MuCLP.Problem.complete_psort (Kind.pred_sort_env_map_of unknowns)
      @@ MuCLP.Problem.complete_tsort
      @@ MuCLP.Problem.aconv_tvar muclp
    in
    (*Debug.print ~id @@ lazy (sprintf "Preprocessed muCLP: %s\n" @@ str_of muclp);*)
    let pfwcsp =
      let pfwcsp =
        let exchange = Option.is_some exc_info in
        Reducer.f ~id ~exchange ~messenger
          ~use_ppm:config.use_parity_progress_measure ~use_scc:config.use_scc
          ~use_alt_dep:config.use_alternation_depth
          ~ignore_nu_components:config.ignore_nu_components muclp unknowns
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
        (MuCLP.Problem.solution * int) Or_error.t =
      let open Or_error.Monad_infix in
      pcsp_solver ~primal >>= fun (module PCSPSolver) ->
      muclp
      |> pfwcsp_of ~id ~messenger ~exc_info (exi_senv, kind_map)
      |> PCSP.Problem.map ~f:Logic.Term.refresh
      |> PCSPSolver.solve
      >>= function
      | PCSP.Problem.Sat _, info -> Ok (MuCLP.Problem.Valid, info)
      | Unsat _, info -> Ok (Invalid, info)
      | Unknown, info -> Ok (Unknown, info)
      | OutSpace _, _ -> failwith "out of space" (* TODO *)
      | Timeout, info -> Ok (Timeout, info)
    in
    let muclp, unknowns =
      let unknowns = (Map.Poly.empty, Map.Poly.empty) in
      if MuCLP.Problem.has_only_forall muclp then
        (* Skolemization is not required *)
        (muclp, unknowns)
      else (
        (* Skolemize existential quantifiers *)
        if false then
          Debug.print ~id
          @@ lazy (sprintf "Input muCLP: %s\n" @@ MuCLP.Problem.str_of muclp);
        let muclp, unknowns = Qelim.elim_exists (muclp, unknowns) in
        Debug.print ~id
        @@ lazy (sprintf "Skolemized: %s\n" @@ MuCLP.Problem.str_of muclp);
        (muclp, unknowns))
    in
    check_forall_only unknowns muclp

  let rec solve_primal ?(id = None) ~messenger ~exc_info flip_on_failure muclp =
    Or_error.Monad_infix.(
      check ~primal:true ~id ~messenger ~exc_info muclp >>= function
      | ((Unknown | Timeout) as r), info ->
          if flip_on_failure then
            solve_dual ~id ~messenger ~exc_info false muclp
          else Ok (r, info)
      | x ->
          Debug.print @@ lazy "primal finished";
          Ok x)

  and solve_dual ?(id = None) ~messenger ~exc_info flip_on_failure muclp =
    Or_error.Monad_infix.(
      check ~primal:false ~id ~messenger ~exc_info (MuCLP.Util.get_dual muclp)
      >>= function
      | ((Unknown | Timeout) as r), info ->
          if flip_on_failure then
            solve_primal ~id ~messenger ~exc_info false muclp
          else Ok (r, info)
      | res, info ->
          Debug.print @@ lazy "dual finished";
          Ok (MuCLP.Problem.flip_solution res, info))

  let solve_primal_dual muclp =
    let open Or_error.Monad_infix in
    assert (config.number_of_pairs >= 1);
    let pool =
      Util.Task.setup_pool ~num_additional_domains:(2 * config.number_of_pairs)
    in
    let rec gen_tasks i =
      if i < config.number_of_pairs then
        let task_primal =
          let id = Some ((i * 2) + 1) in
          Util.Task.async pool (fun () ->
              Debug.print @@ lazy "task_prove";
              solve_primal ~id ~messenger:None ~exc_info:None false muclp)
        in
        let task_dual =
          let id = Some ((i * 2) + 2) in
          Util.Task.async pool (fun () ->
              Debug.print @@ lazy "task_disprove";
              solve_dual ~id ~messenger:None ~exc_info:None false muclp)
        in
        task_primal :: task_dual :: gen_tasks (i + 1)
      else []
    in
    try
      gen_tasks 0 |> Util.Task.await_any_promise pool >>= function
      | sol, info ->
          Debug.print @@ lazy "task over";
          Ok (sol, info)
    with err -> Or_error.of_exn err

  (*
  type info += Examples of ExClauseSet.t

  let send_examples messenger id exs =
    send_boardcast messenger id @@ Examples exs

  let receive_examples messenger_opt id =
    match messenger_opt with
    | None -> Set.Poly.empty
    | Some messenger ->
        receive_all_infos_with messenger id ~filter:(function
          | Examples _ -> true
          | _ -> false)
        |> List.map ~f:(function _, Examples exs -> exs | _ -> Set.Poly.empty)
        |> Set.Poly.union_list
  *)

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
                      ( List.split_n params (List.length params - arity),
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
                          ( List.split_n params (List.length params - arity),
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
                  fst @@ refresh_sort_env_list ~prefix:None uni_params
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
      let g = transitive_closure @@ gen_init_graph muclp.query muclp.preds in
      let reached_pvs pv =
        Set.Poly.map ~f:Ident.pvar_to_tvar
        @@ Set.add (Map.Poly.find_exn g pv).reachable pv
      in
      Debug.print @@ lazy ("dep_pvars_graph:\n" ^ Reducer.DepGraph.str_of g);
      Map.Poly.of_alist_exn
      @@ List.map muclp.preds ~f:(fun pred ->
          ( Ident.pvar_to_tvar pred.name,
            (reached_pvs pred.name, List.length pred.args) ))
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
      let id = id_primal in
      let messenger = messenger_primal in
      Util.Task.async pool (fun () ->
          check ~primal:true ~id ~messenger ~exc_info muclp)
    in
    let task_dual =
      let id = id_dual in
      let messenger = messenger_dual in
      Util.Task.async pool (fun () ->
          check ~primal:false ~id ~messenger ~exc_info
            (MuCLP.Util.get_dual muclp)
          >>= function
          | res, info -> Ok (MuCLP.Problem.flip_solution res, info))
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
      if MuCLP.Problem.has_only_forall muclp then (
        if MuCLP.Problem.has_only_nu muclp then
          Debug.print @@ lazy "vvvv muCLP shape: only forall-nu"
        else if MuCLP.Problem.has_only_mu muclp then
          Debug.print @@ lazy "vvvv muCLP shape: only forall-mu"
        else Debug.print @@ lazy "vvvv muCLP shape: only forall";
        Config.Prove)
      else if MuCLP.Problem.has_only_exists muclp then (
        if MuCLP.Problem.has_only_nu muclp then
          Debug.print @@ lazy "vvvv muCLP shape: only exists-nu"
        else if MuCLP.Problem.has_only_mu muclp then
          Debug.print @@ lazy "vvvv muCLP shape: only exists-mu"
        else Debug.print @@ lazy "vvvv muCLP shape: only exists";
        Config.Disprove)
      else (
        if MuCLP.Problem.has_only_nu muclp then
          Debug.print @@ lazy "vvvv muCLP shape: only nu"
        else if MuCLP.Problem.has_only_mu muclp then
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
          @@ lazy
               "-=-=-=-= proving/disproving exchange learned clauses -=-=-=-=";
          Debug.set_id id_mean;
          preprocess ~id:id_mean ~elim_forall:true ~elim_exists:true
            ~elim_pvar_args:true muclp
          >>= solve_primal_dual_exc)
    >>= function
    | sol, info ->
        Debug.print @@ lazy "=========================";
        let str_sol =
          MuCLP.Problem.(
            if config.output_yes_no then lts_str_of_solution
            else str_of_solution)
            sol
        in
        let str_info =
          match
            ( Hashtbl.Poly.find send_records id_primal,
              Hashtbl.Poly.find send_records id_dual )
          with
          | Some primal_num_sent, Some dual_num_sent ->
              sprintf "%d,%d|%d" info primal_num_sent dual_num_sent
          | _ (*ToDo*) -> sprintf "%d" info
        in
        if print_sol then
          print_endline
          @@
          if config.output_iteration then sprintf "%s,%s" str_sol str_info
          else sprintf "%s" str_sol;
        Or_error.return (sol, str_info, info)

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
        solve ~print_sol:false (MuCLP.Util.of_chc ~print:Debug.print pcsp)
        >>= fun (sol, str_info, info) ->
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
            sprintf "%s,%s" (PCSP.Problem.str_of_solution sol) str_info
          else sprintf "%s" (PCSP.Problem.str_of_solution sol);
        Or_error.return (sol, { PCSatCommon.State.num_cegis_iters = info }))
      pcsp

  let solve_interactive muclp =
    let pre_primal, muclp_primal =
      let bounds, phi, _ =
        if Formula.is_forall muclp.MuCLP.Problem.query then
          Formula.let_forall muclp.query
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
        MuCLP.Problem.make muclp.preds
        @@ Formula.(forall bounds @@ mk_imply pre phi) )
    in
    let pre_dual, muclp_dual =
      let muclp = MuCLP.Util.get_dual muclp in
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
        MuCLP.Problem.make muclp.preds
        @@ Formula.(forall bounds @@ mk_imply pre phi) )
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
          let bpvs =
            Set.Poly.map ord_pvs_primal ~f:(fst >> Ident.pvar_to_tvar)
          in
          (match timeout with
            | None -> PCSPSolver.solve ~bpvs pcsp
            | Some tm ->
                Timer.enable_timeout tm Fn.id ignore
                  (fun () -> PCSPSolver.solve ~bpvs pcsp)
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
                @@ Logic.ExtTerm.to_old_fml Map.Poly.empty (fst pre_primal)
                     Logic.(
                       Term.subst sol @@ ExtTerm.of_old_formula
                       @@ snd pre_primal)
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
                Or_error.return (MuCLP.Problem.Unknown, -1) (*Dummy*))
          | Unsat _, _ ->
              if Formula.is_false pos && Formula.is_false neg then (
                Out_channel.print_endline
                  "maximally weak precondition for dual property:";
                Out_channel.print_endline @@ Formula.str_of unknown;
                Or_error.return (MuCLP.Problem.Unknown, -1) (*Dummy*))
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
          let bpvs = Set.Poly.map ord_pvs_dual ~f:(fst >> Ident.pvar_to_tvar) in
          (match timeout with
            | None -> PCSPSolver.solve ~bpvs pcsp
            | Some tm ->
                Timer.enable_timeout tm Fn.id ignore
                  (fun () -> PCSPSolver.solve ~bpvs pcsp)
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
                @@ Logic.ExtTerm.to_old_fml Map.Poly.empty (fst pre_dual)
                     Logic.(
                       Term.subst sol @@ ExtTerm.of_old_formula @@ snd pre_dual)
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
                Or_error.return (MuCLP.Problem.Unknown, -1) (*Dummy*))
          | Unsat _, _ ->
              if Formula.is_false pos && Formula.is_false neg then (
                Out_channel.print_endline
                  "maximally weak precondition for primal property:";
                Out_channel.print_endline @@ Formula.str_of unknown;
                Or_error.return (MuCLP.Problem.Unknown, -1) (*Dummy*))
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
            MuCLP.Util.query_from_string ~print:Debug.print
            @@ In_channel.(input_line_exn stdin)
          with
          | Ok phi -> refine primal dual unknown (Formula.mk_or pos phi) neg
          | Error msg -> failwith (Error.to_string_hum msg))
      | "neg" -> (
          Out_channel.output_string Out_channel.stdout "negative examples: ";
          Out_channel.flush Out_channel.stdout;
          match
            MuCLP.Util.query_from_string ~print:Debug.print
            @@ In_channel.(input_line_exn stdin)
          with
          | Ok phi -> refine primal dual unknown pos (Formula.mk_or neg phi)
          | Error msg -> failwith (Error.to_string_hum msg))
      | "unknown" ->
          Out_channel.print_endline @@ Formula.str_of unknown;
          refine primal dual unknown pos neg
      | "end" -> Or_error.return (MuCLP.Problem.Unknown, -1) (*Dummy*)
      | _ -> refine primal dual unknown pos neg
    in
    refine (Formula.mk_false ()) (Formula.mk_false ()) (Formula.mk_true ())
      (Formula.mk_false ()) (Formula.mk_false ())

  (** validity checking for Quantitative Fixpoint Logic *)

  let underapprox_of (pred : QFL.Pred.t) =
    let cond, template =
      Templ.underapprox_of
        ~cond_degree:config.quant_underapprox_templ_cond_degree
        ~term_degree:config.quant_underapprox_templ_term_degree pred.args
        pred.body
    in
    ( cond,
      template.templ_params,
      template.templ_constrs,
      { pred with body = template.quant_pred } )

  let delta_of (preds : QFL.Pred.t list) =
    let zero =
      Map.Poly.of_alist_exn
        (List.map preds ~f:(fun pred ->
             (pred.name, (pred.args, T_real.rzero ()))))
    in
    List.map preds ~f:(fun pred ->
        QFL.Pred.simplify
          {
            pred with
            body =
              (let rec aux = function
                 | Term.FunApp (T_bool.IfThenElse, [ cond; t1; t2 ], _) ->
                     T_bool.mk_if_then_else cond (aux t1) (aux t2)
                 | Term.FunApp
                     ( FVar ((Ident.Tvar ("min" | "max") as fvar), sargs, sret),
                       args,
                       _ ) ->
                     Term.mk_fvar_app fvar sargs sret (List.map args ~f:aux)
                 | t ->
                     Normalizer.normalize_term
                     @@ T_real.mk_rsub t (Term.subst_funcs zero t)
               in
               aux pred.body);
          })

  let str_of_sol (name, (args, quant_pred)) =
    sprintf "%s %s |-> %s" (Ident.name_of_tvar name)
      (str_of_sort_env_list Term.str_of_sort args)
      (Term.str_of quant_pred)

  let str_of_templ templ = String.concat_map_list ~sep:", " ~f:str_of_sol templ

  let print_templ templ =
    List.iter templ ~f:(fun (name, (args, quant_pred)) ->
        Debug.print @@ lazy (str_of_sol (name, (args, quant_pred))))

  let str_of_inv_sol (name, (args, pred)) =
    sprintf "%s %s |-> %s" (Ident.name_of_tvar name)
      (str_of_sort_env_list Term.str_of_sort args)
      (Formula.str_of pred)

  let print_inv_templ templ =
    List.iter templ ~f:(fun (name, (args, pred)) ->
        Debug.print @@ lazy (str_of_inv_sol (name, (args, pred))))

  let gen_cache_constr for_prefp (preds : QFL.Pred.t list) fsub pareto_cache =
    let rel =
      match for_prefp with First _ -> Formula.geq | Second _ -> Formula.leq
    in
    let pc_templ_params = ref Map.Poly.empty in
    let pc_constrs =
      List.concat_map preds ~f:(fun pred ->
          match Ident.name_of_tvar pred.name with
          | "Inv" ->
              let lookup name =
                List.find_exn ~f:(fun pred ->
                    String.(Ident.name_of_tvar (fst pred) = name))
                >> snd
              in
              let post =
                let post =
                  lookup "Post"
                    (List.map preds ~f:(fun pred ->
                         (pred.name, (pred.args, pred.body)))
                    @ Map.Poly.to_alist fsub)
                in
                Term.rename
                  (ren_of_sort_env_list (fst post) pred.args)
                  (snd post)
              in
              let post_inv_list =
                List.filter_map pareto_cache ~f:(function
                  | None -> None
                  | Some sol ->
                      let post = lookup "Post" sol in
                      let inv = lookup "Inv" sol in
                      Some
                        ( Term.rename
                            (ren_of_sort_env_list (fst post) pred.args)
                            (snd post),
                          Term.rename
                            (ren_of_sort_env_list (fst inv) pred.args)
                            (snd inv) ))
              in
              Debug.print ~id:None
              @@ lazy
                   (sprintf
                      "finding an inductive invariant for the new \
                       postcondition [%s] using the pareto cache:\n\
                      \  %s"
                      (Term.str_of post)
                      (String.concat ~sep:"\n  "
                         (List.map post_inv_list ~f:(fun (post, inv) ->
                              sprintf "Post |-> %s, Inv |-> %s"
                                (Term.str_of post) (Term.str_of inv)))));
              let posts, invs = List.unzip post_inv_list in
              let atoms =
                Set.concat_map ~f:(function
                  | Atom.App (Psym T_bool.(Eq | Neq), [ t1; t2 ], _) ->
                      Set.Poly.of_list
                        [ T_real.mk_rlt t1 t2; T_real.mk_rgt t1 t2 ]
                  | atm -> Set.Poly.singleton atm)
                @@ Set.Poly.union_list
                @@ uncurry2 Set.union (Term.atoms_of post)
                   :: List.map posts ~f:(Term.atoms_of >> uncurry2 Set.union)
              in
              if false then
                Debug.print ~id:None
                @@ lazy
                     (sprintf "atoms involved in pareto cache:\n%s"
                     @@ String.concat_map_set ~sep:", " ~f:Atom.str_of atoms);
              let r =
                if config.pareto_cache_zero_reward then T_real.rzero ()
                else
                  Term.mk_var
                    (Ident.mk_fresh_tvar ~prefix:(Some "r") ())
                    T_real.SReal
              in
              let ps, ws, wss, w_constrs =
                if true (*ToDo*) then (
                  (* assume that all the postconditions are piecewise constant and have the same brancing structure *)
                  let rec get_leaf_consts = function
                    | Term.FunApp (T_bool.IfThenElse, [ _; t1; t2 ], _) ->
                        get_leaf_consts t1 @ get_leaf_consts t2
                    | t -> [ t ]
                  in
                  (*let rec replace_leaf_consts ts = function
                          | Term.FunApp
                              (T_bool.IfThenElse, [ cond; t1; t2 ], info) ->
                              let t1, ts = replace_leaf_consts ts t1 in
                              let t2, ts = replace_leaf_consts ts t2 in
                              ( Term.FunApp
                                  (T_bool.IfThenElse, [ cond; t1; t2 ], info),
                                ts )
                          | _ -> (List.hd_exn ts, List.tl_exn ts)
                        in*)
                  let ws = get_leaf_consts post in
                  Debug.print ~id:None
                  @@ lazy
                       (sprintf "leaf constants in [%s]:\n  %s"
                          (Term.str_of post)
                       @@ String.concat_map_list ~sep:", " ~f:Term.str_of ws);
                  let ps =
                    List.map ws ~f:(fun _ ->
                        Term.mk_var
                          (Ident.mk_fresh_tvar ~prefix:(Some "p") ())
                          T_real.SReal)
                  in
                  let wss =
                    List.map posts ~f:(fun post ->
                        let ws = get_leaf_consts post in
                        Debug.print ~id:None
                        @@ lazy
                             (sprintf "leaf constants in [%s]:\n  %s"
                                (Term.str_of post)
                             @@ String.concat_map_list ~sep:", " ~f:Term.str_of
                                  ws);
                        ws)
                  in
                  (ps, ws, wss, []))
                else
                  let ps, ws =
                    List.unzip
                    @@ List.init (config.pareto_cache_num_conds + 1)
                         ~f:(fun _i ->
                           let p =
                             Term.mk_var
                               (Ident.mk_fresh_tvar ~prefix:(Some "p") ())
                               T_real.SReal
                           in
                           let w = Ident.mk_fresh_tvar ~prefix:(Some "w") () in
                           pc_templ_params :=
                             Map.add_exn !pc_templ_params ~key:w
                               ~data:T_real.SReal;
                           (p, Term.mk_var w T_real.SReal))
                  in
                  let wss =
                    List.map posts ~f:(fun _ ->
                        List.init (config.pareto_cache_num_conds + 1)
                          ~f:(fun _i ->
                            let w = Ident.mk_fresh_tvar ~prefix:(Some "w") () in
                            pc_templ_params :=
                              Map.add_exn !pc_templ_params ~key:w
                                ~data:T_real.SReal;
                            Term.mk_var w T_real.SReal))
                  in
                  let w_constrs =
                    let conds =
                      List.init (config.pareto_cache_num_conds + 1)
                        ~f:(fun _i ->
                          let templ =
                            Templ.mk_affine
                            @@ Templ.terms_of config.pareto_cache_cond_degree
                                 pred.args
                          in
                          pc_templ_params :=
                            Map.force_merge !pc_templ_params templ.templ_params;
                          templ.quant_pred)
                    in
                    let w = Templ.gen_quant_pc_template conds ws in
                    Debug.print ~id:None
                    @@ lazy
                         (sprintf "generated weight template for [%s]:\n%s"
                            (Term.str_of post) (Term.str_of w));
                    rel w post
                    :: List.map2_exn wss posts ~f:(fun ws post ->
                        let w = Templ.gen_quant_pc_template conds ws in
                        Debug.print ~id:None
                        @@ lazy
                             (sprintf "generated weight template for [%s]:\n%s"
                                (Term.str_of post) (Term.str_of w));
                        rel post w)
                  in
                  (ps, ws, wss, w_constrs)
              in
              let pres =
                (if config.pareto_cache_zero_reward then []
                 else [ Formula.geq r (T_real.rzero ()) ])
                @ Formula.leq
                    (T_real.mk_rsum (T_real.rzero ()) ps)
                    (T_real.rone ())
                  :: List.map ps ~f:(fun p -> Formula.geq p (T_real.rzero ()))
              in
              w_constrs
              @ List.map
                  ~f:
                    (Formula.subst_funcs
                       (match for_prefp with
                       | First prefp_sub -> prefp_sub
                       | Second
                           ( _prefp_templ_preds,
                             _rank_templ_preds,
                             postfp_templ_preds,
                             _ua_preds_delta ) ->
                           Map.Poly.of_alist_exn postfp_templ_preds))
              @@
              if false then (
                let param_inv = Ident.mk_fresh_tvar ~prefix:(Some "inv") () in
                let param_invs =
                  List.map invs ~f:(fun _ ->
                      Ident.mk_fresh_tvar ~prefix:(Some "inv") ())
                in
                pc_templ_params :=
                  Map.force_merge !pc_templ_params
                    (Map.Poly.of_alist_exn
                    @@ (param_inv, T_real.SReal)
                       :: List.map param_invs ~f:(fun p -> (p, T_real.SReal)));
                (Formula.mk_imply
                   (Formula.and_of @@ pres
                   @ List.map2_exn param_invs wss ~f:(fun param_inv ws ->
                       rel
                         (Term.mk_var param_inv T_real.SReal)
                         (T_real.mk_rsum r
                            (List.map2_exn ps ws ~f:T_real.mk_rmul))))
                @@ rel
                     (Term.mk_var param_inv T_real.SReal)
                     (T_real.mk_rsum r @@ List.map2_exn ps ws ~f:T_real.mk_rmul)
                )
                :: rel
                     (Term.fvar_app_of_senv pred.name pred.args T_real.SReal)
                     (Term.mk_var param_inv T_real.SReal)
                :: List.map2_exn param_invs invs ~f:(fun param_inv inv ->
                    rel (Term.mk_var param_inv T_real.SReal) inv))
              else
                [
                  Formula.mk_imply
                    (Formula.and_of @@ pres
                    @ List.map2_exn invs wss ~f:(fun inv ws ->
                        rel inv
                          (T_real.mk_rsum r
                          @@ List.map2_exn ps ws ~f:T_real.mk_rmul)))
                  @@ rel
                       (Term.fvar_app_of_senv pred.name pred.args T_real.SReal)
                       (T_real.mk_rsum r
                       @@ List.map2_exn ps ws ~f:T_real.mk_rmul);
                ]
          | "Post" -> []
          | _ -> (
              match for_prefp with
              | First prefp_sub ->
                  List.map ~f:(Formula.subst_funcs prefp_sub)
                  @@ List.map (Term.elim_min_max_list pred.body) ~f:(fun body ->
                      rel
                        (Term.fvar_app_of_senv pred.name pred.args T_real.SReal)
                        body)
              | Second
                  ( prefp_templ_preds,
                    rank_templ_preds,
                    postfp_templ_preds,
                    (ua_preds_delta : QFL.Pred.t list) ) ->
                  let postfp_args, postfp_body =
                    List.Assoc.find_exn ~equal:Stdlib.( = ) postfp_templ_preds
                      pred.name
                  in
                  let prefp_args, prefp_body =
                    List.Assoc.find_exn ~equal:Stdlib.( = ) prefp_templ_preds
                      pred.name
                  in
                  let rank_args, rank_body =
                    List.Assoc.find_exn ~equal:Stdlib.( = ) rank_templ_preds
                      pred.name
                  in
                  let ua_pred_delta =
                    List.find_exn ua_preds_delta ~f:(fun pred' ->
                        Stdlib.( = ) pred'.name pred.name)
                  in
                  let rank_sub = Map.Poly.of_alist_exn rank_templ_preds in
                  Formula.leq postfp_body
                    (Term.rename
                       (LogicOld.ren_of_sort_env_list prefp_args postfp_args)
                       prefp_body)
                  :: (List.map
                        ~f:
                          (Formula.subst_funcs
                             (Map.Poly.of_alist_exn postfp_templ_preds))
                     @@ List.map (Term.elim_min_max_list pred.body)
                          ~f:(fun body ->
                            Formula.geq body
                              (Term.fvar_app_of_senv pred.name pred.args
                                 T_real.SReal)))
                  @ List.map
                      ~f:
                        (Formula.subst_funcs
                           (Map.Poly.of_alist_exn prefp_templ_preds))
                  @@ List.map (Term.elim_min_max_list pred.body) ~f:(fun body ->
                      Formula.geq
                        (Term.fvar_app_of_senv pred.name pred.args T_real.SReal)
                        body)
                  @ List.map
                      (Term.elim_min_max_list
                      @@ Term.subst_funcs rank_sub ua_pred_delta.body)
                      ~f:(fun body ->
                        Formula.leq
                          (T_real.mk_radd
                             (Term.rename
                                (LogicOld.ren_of_sort_env_list
                                   ua_pred_delta.args rank_args)
                                body)
                             (Term.rename
                                (LogicOld.ren_of_sort_env_list prefp_args
                                   rank_args)
                                prefp_body))
                          rank_body)))
    in
    (pc_constrs, !pc_templ_params)

  let cgen_pqes_lb (qfl : QFL.Problem.t) query_fml fsub pareto_cache =
    let query_fml = Formula.elim_min_max_list query_fml in
    let conds, templ_paramss, templ_constrss, ua_preds =
      List.unzip4 @@ List.map qfl.preds ~f:underapprox_of
    in
    Debug.print ~id:None
    @@ lazy
         (sprintf "\nunderapproximated:\n%s\n" @@ QFL.Pred.str_of_list ua_preds);
    let strengthen_guard gen =
      List.unzip
      @@ List.map2_exn qfl.preds conds ~f:(fun pred cond ->
          let template : Templ.templ_quant_pred =
            gen pred.args pred.body pred.annots
          in
          let templ_params, quant_pred =
            match cond with
            | None -> (template.templ_params, template.quant_pred)
            | Some cond ->
                let templ_params, quant_pred =
                  if false then
                    let templ =
                      Templ.mk_affine
                      @@ Templ.terms_of
                           config.quant_prefp_templ_term_degree (*ToDo*)
                           pred.args
                    in
                    (templ.templ_params, templ.quant_pred)
                  else (Map.Poly.empty, T_real.rzero ())
                in
                ( Map.force_merge template.templ_params templ_params,
                  T_bool.mk_if_then_else
                    (T_bool.of_formula @@ Formula.geq cond (T_real.rzero ()))
                    template.quant_pred quant_pred )
          in
          (templ_params, (pred.name, (pred.args, quant_pred))))
    in
    let prefp_templ_paramss, prefp_templ_preds =
      strengthen_guard
        (Templ.gen_quant_template ~num_conds:config.quant_prefp_templ_num_conds
           ~use_orig_ite:config.quant_prefp_templ_use_orig_ite
           ~cond_degree:config.quant_prefp_templ_cond_degree
           ~term_degree:config.quant_prefp_templ_term_degree)
    in
    let rank_templ_paramss, rank_templ_preds =
      strengthen_guard
        (Templ.gen_quant_template ~num_conds:config.quant_rank_templ_num_conds
           ~use_orig_ite:config.quant_rank_templ_use_orig_ite
           ~cond_degree:config.quant_rank_templ_cond_degree
           ~term_degree:config.quant_rank_templ_term_degree)
    in
    let coeffs = ref [] in
    let postfp_templ_paramss, postfp_templ_preds =
      strengthen_guard
        (Templ.gen_quant_template ~coeffs:(Some coeffs)
           ~num_conds:config.quant_postfp_templ_num_conds
           ~use_orig_ite:config.quant_postfp_templ_use_orig_ite
           ~cond_degree:config.quant_postfp_templ_cond_degree
           ~term_degree:config.quant_postfp_templ_term_degree)
    in
    if not @@ List.is_empty prefp_templ_preds then (
      Debug.print @@ lazy "templates for prefixpoint:";
      print_templ prefp_templ_preds);
    if not @@ List.is_empty rank_templ_preds then (
      Debug.print @@ lazy "\ntemplates for ranking supermartingales:";
      print_templ rank_templ_preds);
    if not @@ List.is_empty postfp_templ_preds then (
      Debug.print @@ lazy "\ntemplates for postfixpoint:";
      print_templ postfp_templ_preds);
    let prefp_sub = Map.Poly.of_alist_exn prefp_templ_preds in
    let rank_sub = Map.Poly.of_alist_exn rank_templ_preds in
    let postfp_sub = Map.Poly.of_alist_exn postfp_templ_preds in
    let ua_preds_delta = delta_of ua_preds in
    Debug.print ~id:None
    @@ lazy (sprintf "\ndelta:\n%s\n" @@ QFL.Pred.str_of_list ua_preds_delta);
    let constrs =
      List.concat templ_constrss
      @ (if config.quant_postfp_force_non_const then
           [
             Formula.or_of
               (List.map !coeffs ~f:(fun c -> Formula.neq c (T_real.rzero ())));
           ]
         else [])
      @ List.map
          (prefp_templ_preds @ rank_templ_preds @ postfp_templ_preds)
          ~f:(fun (_, (_, quant_pred)) ->
            Formula.geq quant_pred (T_real.rzero ()))
      @ List.map postfp_templ_preds
          ~f:(fun (name, (postfp_args, postfp_body)) ->
            let prefp_args, prefp_body =
              List.Assoc.find_exn ~equal:Stdlib.( = ) prefp_templ_preds name
            in
            Formula.leq postfp_body
              (Term.rename
                 (LogicOld.ren_of_sort_env_list prefp_args postfp_args)
                 prefp_body))
      @ (List.map ~f:(Formula.subst_funcs postfp_sub)
        @@ query_fml
        @ List.concat_map ua_preds ~f:(fun pred ->
            List.map (Term.elim_min_max_list pred.body) ~f:(fun body ->
                Formula.geq body
                  (Term.fvar_app_of_senv pred.name pred.args T_real.SReal))))
      @ List.map ~f:(Formula.subst_funcs prefp_sub)
      @@ List.concat_map ua_preds ~f:(fun pred ->
          List.map (Term.elim_min_max_list pred.body) ~f:(fun body ->
              Formula.geq
                (Term.fvar_app_of_senv pred.name pred.args T_real.SReal)
                body))
      @ List.concat_map rank_templ_preds
          ~f:(fun (name, (rank_args, rank_body)) ->
            let ua_pred_delta =
              List.find_exn ua_preds_delta ~f:(fun pred ->
                  Stdlib.( = ) pred.name name)
            in
            let prefp_args, prefp_body =
              List.Assoc.find_exn ~equal:Stdlib.( = ) prefp_templ_preds name
            in
            List.map
              (Term.elim_min_max_list
              @@ Term.subst_funcs rank_sub ua_pred_delta.body)
              ~f:(fun body ->
                Formula.leq
                  (T_real.mk_radd
                     (Term.rename
                        (LogicOld.ren_of_sort_env_list ua_pred_delta.args
                           rank_args)
                        body)
                     (Term.rename
                        (LogicOld.ren_of_sort_env_list prefp_args rank_args)
                        prefp_body))
                  rank_body))
    in
    let templ_params =
      Map.force_merge_list @@ templ_paramss @ prefp_templ_paramss
      @ postfp_templ_paramss @ rank_templ_paramss
    in
    let main, backup =
      match config.enable_pareto_caching with
      | Some thr when List.length pareto_cache >= thr ->
          let pc_constrs, pc_templ_params =
            gen_cache_constr
              (Second
                 ( prefp_templ_preds,
                   rank_templ_preds,
                   postfp_templ_preds,
                   ua_preds_delta ))
              ua_preds fsub pareto_cache
          in
          let pc_constrs =
            List.concat templ_constrss
            @ List.filter_map (prefp_templ_preds @ rank_templ_preds)
                ~f:(fun (name, (_, quant_pred)) ->
                  if String.(Ident.name_of_tvar name <> "Inv") then
                    Some (Formula.geq quant_pred (T_real.rzero ()))
                  else None)
            @ List.map postfp_templ_preds ~f:(fun (_, (_, quant_pred)) ->
                Formula.geq quant_pred (T_real.rzero ()))
            @ List.map ~f:(Formula.subst_funcs postfp_sub) query_fml
            @ pc_constrs
          in
          ( ( ( Some ua_preds,
                prefp_templ_preds,
                rank_templ_preds,
                postfp_templ_preds ),
              PCSP.Problem.make ~prefix:(Some "q") pc_constrs
              @@ SMT.Problem.
                   {
                     uni_senv = Map.Poly.empty;
                     exi_senv = Map.force_merge templ_params pc_templ_params;
                     kind_map = Map.Poly.empty (*ToDo*);
                     fenv = Map.Poly.empty;
                     dtenv = Map.Poly.empty;
                   } ),
            Some
              ( ( Some ua_preds,
                  prefp_templ_preds,
                  rank_templ_preds,
                  postfp_templ_preds ),
                PCSP.Problem.make ~prefix:(Some "q") constrs
                @@ SMT.Problem.
                     {
                       uni_senv = Map.Poly.empty;
                       exi_senv = templ_params;
                       kind_map = Map.Poly.empty (*ToDo*);
                       fenv = Map.Poly.empty;
                       dtenv = Map.Poly.empty;
                     } ) )
      | _ ->
          ( ( ( Some ua_preds,
                prefp_templ_preds,
                rank_templ_preds,
                postfp_templ_preds ),
              PCSP.Problem.make ~prefix:(Some "q") constrs
              @@ SMT.Problem.
                   {
                     uni_senv = Map.Poly.empty;
                     exi_senv = templ_params;
                     kind_map = Map.Poly.empty (*ToDo*);
                     fenv = Map.Poly.empty;
                     dtenv = Map.Poly.empty;
                   } ),
            None )
    in
    (main, backup)

  let cgen_pqes_ub (qfl : QFL.Problem.t) query_fml fsub pareto_cache =
    let query_fml = Formula.elim_min_max_list query_fml in
    let prefp_templ_paramss, prefp_templ_preds =
      List.unzip
      @@ List.map qfl.preds ~f:(fun pred ->
          let template =
            Templ.gen_quant_template
              ~num_conds:config.quant_prefp_templ_num_conds
              ~use_orig_ite:config.quant_prefp_templ_use_orig_ite
              ~cond_degree:config.quant_prefp_templ_cond_degree
              ~term_degree:config.quant_prefp_templ_term_degree pred.args
              pred.body pred.annots
          in
          (template.templ_params, (pred.name, (pred.args, template.quant_pred))))
    in
    if not @@ List.is_empty prefp_templ_preds then (
      Debug.print @@ lazy "templates for prefixpoint:";
      print_templ prefp_templ_preds);
    let prefp_sub = Map.Poly.of_alist_exn prefp_templ_preds in
    let constrs =
      List.map prefp_templ_preds ~f:(fun (_, (_, quant_pred)) ->
          Formula.geq quant_pred (T_real.rzero ()))
      @ List.map ~f:(Formula.subst_funcs prefp_sub)
      @@ query_fml
      @ List.concat_map qfl.preds ~f:(fun pred ->
          List.map (Term.elim_min_max_list pred.body) ~f:(fun body ->
              Formula.geq
                (Term.fvar_app_of_senv pred.name pred.args T_real.SReal)
                body))
    in
    let templ_params = Map.force_merge_list prefp_templ_paramss in
    let main, backup =
      match config.enable_pareto_caching with
      | Some thr when List.length pareto_cache >= thr ->
          let pc_constrs, pc_templ_params =
            gen_cache_constr (First prefp_sub) qfl.preds fsub pareto_cache
          in
          let pc_constrs =
            List.map prefp_templ_preds ~f:(fun (_, (_, quant_pred)) ->
                Formula.geq quant_pred (T_real.rzero ()))
            @ List.map ~f:(Formula.subst_funcs prefp_sub) query_fml
            @ pc_constrs
          in
          ( ( (None, prefp_templ_preds, [], []),
              PCSP.Problem.make pc_constrs
              @@ SMT.Problem.
                   {
                     uni_senv = Map.Poly.empty;
                     exi_senv = Map.force_merge templ_params pc_templ_params;
                     kind_map = Map.Poly.empty (*ToDo*);
                     fenv = Map.Poly.empty;
                     dtenv = Map.Poly.empty;
                   } ),
            Some
              ( (None, prefp_templ_preds, [], []),
                PCSP.Problem.make constrs
                @@ SMT.Problem.
                     {
                       uni_senv = Map.Poly.empty;
                       exi_senv = templ_params;
                       kind_map = Map.Poly.empty (*ToDo*);
                       fenv = Map.Poly.empty;
                       dtenv = Map.Poly.empty;
                     } ) )
      | _ ->
          ( ( (None, prefp_templ_preds, [], []),
              PCSP.Problem.make constrs
              @@ SMT.Problem.
                   {
                     uni_senv = Map.Poly.empty;
                     exi_senv = templ_params;
                     kind_map = Map.Poly.empty (*ToDo*);
                     fenv = Map.Poly.empty;
                     dtenv = Map.Poly.empty;
                   } ),
            None )
    in
    (main, backup)

  let div_ceil n d = if n % d = 0 then n / d else (n / d) + 1

  let solve_constrs templ_params constrs =
    let pqes =
      PCSP.Problem.make ~prefix:(Some "q") constrs
      @@ SMT.Problem.
           {
             uni_senv = Map.Poly.empty;
             exi_senv = templ_params;
             kind_map = Map.Poly.empty (*ToDo*);
             fenv = Map.Poly.empty;
             dtenv = Map.Poly.empty;
           }
    in
    Debug.print ~id:None
    @@ lazy (sprintf "******* Generated PQEs:\n%s" @@ PCSP.Problem.str_of pqes);
    let open Or_error.Monad_infix in
    pcsp_solver ~primal:true >>= fun (module PCSPSolver) ->
    PCSPSolver.solve pqes >>= function
    | PCSP.Problem.Sat model, _ ->
        Ok
          (Some
             (Map.Poly.mapi templ_params ~f:(fun ~key ~data:_ ->
                  match Map.Poly.find model key with
                  | Some t -> t
                  | None -> Logic.RealTerm.rzero () (*ToDo*))))
    | Unsat _, _ ->
        Debug.print @@ lazy "the templates used may not be expressive enough";
        Ok None
    | Unknown, _ ->
        Debug.print
        @@ lazy
             "the backend PQE solver failed or the templates used may not be \
              expressive enough";
        Ok None
    | OutSpace _, _ ->
        Debug.print @@ lazy "out of space" (* TODO *);
        Ok None
    | Timeout, _ ->
        Debug.print @@ lazy "timeout";
        Ok None

  let conv tsub param_senv constrs =
    if List.is_empty param_senv then Set.Poly.empty
    else
      let param_constrs' =
        Set.Poly.map (Set.Poly.of_list constrs)
          ~f:
            (Formula.subst
               (Map.Poly.filter_keys tsub
                  ~f:(List.Assoc.mem ~equal:Stdlib.( = ) param_senv >> not))
            >> Normalizer.normalize >> Evaluator.simplify)
      in
      Debug.print @@ lazy "begin qelim";
      let param_constrs' =
        Set.concat_map param_constrs' ~f:(fun phi ->
            Set.concat_map (Formula.conjuncts_of phi) ~f:(fun phi ->
                let senv, phi =
                  Formula.rm_quant
                  @@ Z3Smt.Z3interface.qelim ~id:None
                       ~fenv:(LogicOld.get_fenv ())
                  @@ Formula.forall
                       (Set.to_list
                       @@ Set.filter
                            (Formula.term_sort_env_of phi)
                            ~f:
                              (fst
                              >> List.Assoc.mem ~equal:Stdlib.( = ) param_senv
                              >> not))
                       phi
                in
                Set.Poly.map
                  (Formula.to_cnf ~process_pure:true phi)
                  ~f:(Formula.forall (Set.to_list senv))))
      in
      Debug.print @@ lazy "end qelim";
      assert (
        Set.for_all param_constrs' ~f:(fun phi ->
            Set.is_subset (Formula.fvs_of phi)
              ~of_:(Set.Poly.of_list @@ List.map ~f:fst param_senv)));
      Debug.print
      @@ lazy
           (sprintf "parameter constraints: %s |-> %s"
              (str_of_sort_env_list Term.str_of_sort param_senv)
              (Formula.str_of @@ Formula.and_of @@ Set.to_list param_constrs'));
      param_constrs'

  let simul_inv_syn = true

  let rec gen_inv_cnstr inv_sub conds = function
    | Term.FunApp (T_bool.IfThenElse, [ cond; t1; t2 ], _) ->
        Set.Poly.union_list
        @@ List.map
             (Formula.disjuncts_list_of @@ Evaluator.simplify
            @@ Formula.of_bool_term cond)
             ~f:(fun cond -> gen_inv_cnstr inv_sub (Set.add conds cond) t1)
        @ List.map
            (Formula.disjuncts_list_of @@ Evaluator.simplify
            @@ Formula.of_neg_bool_term cond)
            ~f:(fun cond -> gen_inv_cnstr inv_sub (Set.add conds cond) t2)
    | Term.FunApp (T_real.RAdd, [ t1; t2 ], _) ->
        Set.union
          (gen_inv_cnstr inv_sub conds t1)
          (gen_inv_cnstr inv_sub conds t2)
    | Term.FunApp (T_real.RMul, [ t1; t2 ], _) ->
        Set.union
          (gen_inv_cnstr inv_sub conds t1)
          (gen_inv_cnstr inv_sub conds t2)
    | Term.FunApp (FVar (Ident.Tvar ("min" | "max"), _, _), args, _) ->
        Set.Poly.union_list @@ List.map ~f:(gen_inv_cnstr inv_sub conds) args
    | Term.FunApp (FVar (fvar, _, _), args, _) -> (
        match Map.Poly.find inv_sub fvar with
        | Some (senv, phi) ->
            let sub =
              Map.Poly.of_alist_exn
              @@ List.map2_exn senv args ~f:(fun (x, _) t -> (x, t))
            in
            Set.Poly.map
              (Formula.to_cnf ~process_pure:true @@ Formula.subst sub phi)
              ~f:(fun conc -> (conds, conc))
        | None -> Set.Poly.empty (*ToDo*))
    | _ (*ToDo*) -> Set.Poly.empty

  let gen_inv_constrs init inv_sub invmap (preds : QFL.Pred.t list) =
    match init with
    | None -> []
    | Some (init_name, init_args) ->
        Set.to_list
        @@ Set.Poly.union_list
             ((let inv_args, inv_body = Map.find_exn inv_sub init_name in
               Formula.to_cnf ~process_pure:true
               @@ Formula.subst
                    (Map.Poly.of_alist_exn
                    @@ List.map2_exn inv_args init_args ~f:(fun (x, _) t ->
                        (x, t)))
                    inv_body)
             :: List.map preds ~f:(fun pred ->
                 let constrs =
                   let cond' =
                     let inv_args, inv_body = Map.find_exn inv_sub pred.name in
                     Formula.rename
                       (LogicOld.ren_of_sort_env_list inv_args pred.args)
                       inv_body
                   in
                   let cond' =
                     if true then cond'
                     else
                       match Map.Poly.find invmap pred.name with
                       | None -> cond'
                       | Some (inv_args, inv_body) ->
                           Formula.mk_and cond'
                             (Formula.rename
                                (LogicOld.ren_of_sort_env_list inv_args
                                   pred.args)
                                inv_body)
                   in
                   Set.concat_map (Formula.disjuncts_of cond') ~f:(fun cond' ->
                       Set.Poly.filter_map ~f:(fun (conds, conc) ->
                           let c =
                             Evaluator.simplify @@ Formula.and_of @@ Set.to_list
                             @@ Set.add conds cond'
                           in
                           if Formula.is_true c then Some conc
                           else if Formula.is_false c then None
                           else Some (Formula.mk_imply c conc))
                       @@ gen_inv_cnstr inv_sub Set.Poly.empty pred.body)
                 in
                 if false then
                   Set.iter constrs ~f:(fun c ->
                       Debug.print @@ lazy ("c: " ^ Formula.str_of c));
                 constrs))

  let gen_inv_templ init param_senv (preds : QFL.Pred.t list) =
    match init with
    | None -> ([], [])
    | Some _ ->
        let inv_templ_paramss, inv_templ_preds =
          List.unzip
          @@ List.map preds ~f:(fun pred ->
              let template =
                Templ.gen_dnf ~eq_atom:false ~real_coeff:true ~ignore_hole:true
                  ~br_bools:false ~only_bools:false
                  {
                    consts = [];
                    terms = [];
                    quals = [];
                    shp = config.quant_omega_regular_inv_shape;
                    ubc = None;
                    ubd = None;
                    s = Set.Poly.empty;
                  }
                  { bec = None } (param_senv @ pred.args)
              in
              (template.templ_params, (pred.name, (pred.args, template.pred))))
        in
        if not @@ List.is_empty inv_templ_preds then (
          Debug.print @@ lazy "templates for invariants:";
          print_inv_templ inv_templ_preds);
        (inv_templ_paramss, inv_templ_preds)

  let gen_rank_templ param_senv (preds : QFL.Pred.t list) =
    let rank_templ_paramss, rank_templ_preds =
      List.unzip
      @@ List.map preds ~f:(fun pred ->
          let template =
            Templ.gen_quant_template
              ~num_conds:config.quant_rank_templ_num_conds
              ~use_orig_ite:config.quant_rank_templ_use_orig_ite
              ~cond_degree:config.quant_rank_templ_cond_degree
              ~term_degree:config.quant_rank_templ_term_degree
              (param_senv @ pred.args) pred.body pred.annots
          in
          (template.templ_params, (pred.name, (pred.args, template.quant_pred))))
    in
    if not @@ List.is_empty rank_templ_preds then (
      Debug.print @@ lazy "templates for ranking supermartingales:";
      print_templ rank_templ_preds);
    (rank_templ_paramss, rank_templ_preds)

  let gen_rank_constrs inv_sub invmap pred_eps_set rank_sub rank_templ_preds =
    List.concat_map rank_templ_preds ~f:(fun (name, (args, quant_pred)) ->
        List.map
          (match
             Map.Poly.find (if simul_inv_syn then inv_sub else invmap) name
           with
          | None -> [ Fn.id ]
          | Some (inv_args, inv) ->
              let inv =
                Formula.rename (LogicOld.ren_of_sort_env_list inv_args args) inv
              in
              List.map (Formula.disjuncts_list_of inv) ~f:Formula.mk_imply)
          ~f:(fun f -> f @@ Formula.geq quant_pred (T_real.rzero ())))
    @ List.concat_map (Set.to_list pred_eps_set)
        ~f:(fun ((pred : QFL.Pred.t), eps) ->
          let rank_args, rank_body = Map.find_exn rank_sub pred.name in
          List.map
            (match
               Map.Poly.find
                 (if simul_inv_syn then inv_sub else invmap)
                 pred.name
             with
            | None -> [ Fn.id ]
            | Some (inv_args, inv) ->
                let inv =
                  Formula.rename
                    (LogicOld.ren_of_sort_env_list inv_args pred.args)
                    inv
                in
                List.map (Formula.disjuncts_list_of inv) ~f:Formula.mk_imply)
            ~f:(fun f ->
              f
              @@ Formula.geq
                   (Term.rename
                      (LogicOld.ren_of_sort_env_list rank_args pred.args)
                      rank_body)
                   (T_real.mk_radd (Term.mk_var eps T_real.SReal)
                   @@ Term.subst_funcs rank_sub pred.body)))

  let synthesize_ssm (qfl : QFL.Problem.t)
      (init, invmap, param_senv, param_constrs) =
    let d_div_2 = div_ceil (QFL.Problem.depth_of qfl) 2 in
    let rec loop param_constrs lexmap j =
      if j <= d_div_2 then (
        let preds = Set.Poly.of_list qfl.preds in
        Debug.print ~id:None
        @@ lazy
             (sprintf "\n***synthesizing ranking supermartingales at level %d\n"
                j);
        let inv_templ_paramss, inv_templ_preds =
          gen_inv_templ init param_senv qfl.preds
        in
        let inv_sub = Map.Poly.of_alist_exn inv_templ_preds in
        let rank_templ_paramss, rank_templ_preds =
          gen_rank_templ param_senv qfl.preds
        in
        let rank_sub = Map.Poly.of_alist_exn rank_templ_preds in
        let pred_eps_set =
          Set.Poly.map preds ~f:(fun pred ->
              let eps = Ident.mk_fresh_tvar ~prefix:(Some "eps") () in
              Debug.print
              @@ lazy
                   (sprintf "%s |-> %s"
                      (Ident.name_of_tvar pred.name)
                      (Ident.name_of_tvar eps));
              (pred, eps))
        in
        let constrs_inv = gen_inv_constrs init inv_sub invmap qfl.preds in
        let constrs_rank =
          (Set.to_list
          @@ Set.Poly.map pred_eps_set ~f:(fun (pred, eps) ->
              if QFL.Problem.level_of qfl pred.name = (2 * j) - 1 then
                Formula.eq (Term.mk_var eps T_real.SReal) (T_real.rone ())
              else if QFL.Problem.level_of qfl pred.name < (2 * j) - 1 then
                Formula.lt (Term.mk_var eps T_real.SReal) (T_real.rzero ())
              else Formula.eq (Term.mk_var eps T_real.SReal) (T_real.rzero ()))
          )
          @ gen_rank_constrs inv_sub invmap pred_eps_set rank_sub
              rank_templ_preds
        in
        let constrs = Set.to_list param_constrs @ constrs_inv @ constrs_rank in
        let templ_params =
          Map.force_merge_list
          @@ Map.Poly.of_alist_exn param_senv
             :: (Map.of_set_exn
                @@ Set.Poly.map pred_eps_set ~f:(fun (_, eps) ->
                    (eps, T_real.SReal)))
             :: rank_templ_paramss
          @ List.map ~f:Logic.to_old_sort_env_map inv_templ_paramss
        in
        match solve_constrs templ_params constrs with
        | Ok (Some model) ->
            let tsub =
              Logic.ExtTerm.to_old_subst Map.Poly.empty Map.Poly.empty model
            in
            let param_constrs' = conv tsub param_senv constrs in
            Debug.print @@ lazy "*************************************";
            List.iter inv_templ_preds ~f:(fun (name, (args, pred)) ->
                let inv = Evaluator.simplify @@ Formula.subst tsub pred in
                Debug.print
                @@ lazy
                     (sprintf "synthesized invariant for %s: %s |-> %s"
                        (Ident.name_of_tvar name)
                        (str_of_sort_env_list Term.str_of_sort args)
                        (Formula.str_of inv)));
            Debug.print @@ lazy "*************************************";
            let lexmap' =
              let ranks =
                List.map rank_templ_preds ~f:(fun (name, (args, quant_pred)) ->
                    ( name,
                      ( args,
                        Evaluator.simplify_term @@ Term.subst tsub quant_pred )
                    ))
              in
              List.fold ~init:lexmap qfl.preds ~f:(fun lexmap pred ->
                  let rank_args, rank_body =
                    List.Assoc.find_exn ~equal:Stdlib.( = ) ranks pred.name
                  in
                  let rank =
                    Term.rename
                      (LogicOld.ren_of_sort_env_list rank_args pred.args)
                      rank_body
                  in
                  Debug.print
                  @@ lazy
                       (sprintf
                          "synthesized ranking supermartingale for (%s, %d, \
                           %d): %s |-> %s"
                          (Ident.name_of_tvar pred.name)
                          j 0
                          (str_of_sort_env_list Term.str_of_sort pred.args)
                          (Term.str_of rank));
                  Map.Poly.add_exn lexmap ~key:(pred.name, j, 0) ~data:rank)
            in
            Debug.print @@ lazy "*************************************";
            loop param_constrs' lexmap' (j + 1)
        | Ok None -> None
        | Error err -> failwith (Error.to_string_hum err))
      else Some lexmap
    in
    loop param_constrs Map.Poly.empty 1

  let synthesize_gssm (qfl : QFL.Problem.t)
      (init, invmap, param_senv, param_constrs) =
    let d_div_2 = div_ceil (QFL.Problem.depth_of qfl) 2 in
    let rec loop param_constrs lexmap j =
      if j <= d_div_2 then (
        let preds =
          Set.filter (Set.Poly.of_list qfl.preds) ~f:(fun pred ->
              QFL.Problem.level_of qfl pred.name >= (2 * j) - 1)
        in
        Debug.print ~id:None
        @@ lazy
             (sprintf "\n***synthesizing ranking supermartingales at level %d\n"
                j);
        let inv_templ_paramss, inv_templ_preds =
          gen_inv_templ init param_senv qfl.preds
        in
        let inv_sub = Map.Poly.of_alist_exn inv_templ_preds in
        let rank_templ_paramss, rank_templ_preds =
          gen_rank_templ param_senv qfl.preds
        in
        let rank_sub = Map.Poly.of_alist_exn rank_templ_preds in
        let pred_eps_set =
          Set.Poly.map preds ~f:(fun pred ->
              let eps = Ident.mk_fresh_tvar ~prefix:(Some "eps") () in
              Debug.print
              @@ lazy
                   (sprintf "%s |-> %s"
                      (Ident.name_of_tvar pred.name)
                      (Ident.name_of_tvar eps));
              (pred, eps))
        in
        let constrs_inv = gen_inv_constrs init inv_sub invmap qfl.preds in
        let constrs_rank =
          (Set.to_list
          @@ Set.Poly.map pred_eps_set ~f:(fun (pred, eps) ->
              if QFL.Problem.level_of qfl pred.name = (2 * j) - 1 then
                Formula.eq (Term.mk_var eps T_real.SReal) (T_real.rone ())
              else Formula.eq (Term.mk_var eps T_real.SReal) (T_real.rzero ()))
          )
          @ gen_rank_constrs inv_sub invmap pred_eps_set rank_sub
              rank_templ_preds
        in
        let constrs = Set.to_list param_constrs @ constrs_inv @ constrs_rank in
        let templ_params =
          Map.force_merge_list
          @@ Map.Poly.of_alist_exn param_senv
             :: (Map.of_set_exn
                @@ Set.Poly.map pred_eps_set ~f:(fun (_, eps) ->
                    (eps, T_real.SReal)))
             :: rank_templ_paramss
          @ List.map ~f:Logic.to_old_sort_env_map inv_templ_paramss
        in
        match solve_constrs templ_params constrs with
        | Ok (Some model) ->
            let tsub =
              Logic.ExtTerm.to_old_subst Map.Poly.empty Map.Poly.empty model
            in
            let param_constrs' = conv tsub param_senv constrs in
            Debug.print @@ lazy "*************************************";
            List.iter inv_templ_preds ~f:(fun (name, (args, pred)) ->
                let inv = Evaluator.simplify @@ Formula.subst tsub pred in
                Debug.print
                @@ lazy
                     (sprintf "synthesized invariant for %s: %s |-> %s"
                        (Ident.name_of_tvar name)
                        (str_of_sort_env_list Term.str_of_sort args)
                        (Formula.str_of inv)));
            Debug.print @@ lazy "*************************************";
            let lexmap' =
              let ranks =
                List.map rank_templ_preds ~f:(fun (name, (args, quant_pred)) ->
                    ( name,
                      ( args,
                        Evaluator.simplify_term @@ Term.subst tsub quant_pred )
                    ))
              in
              List.fold ~init:lexmap qfl.preds ~f:(fun lexmap pred ->
                  let rank_args, rank_body =
                    List.Assoc.find_exn ~equal:Stdlib.( = ) ranks pred.name
                  in
                  let rank =
                    Term.rename
                      (LogicOld.ren_of_sort_env_list rank_args pred.args)
                      rank_body
                  in
                  Debug.print
                  @@ lazy
                       (sprintf
                          "synthesized ranking supermartingale for (%s, %d, \
                           %d): %s |-> %s"
                          (Ident.name_of_tvar pred.name)
                          j 0
                          (str_of_sort_env_list Term.str_of_sort pred.args)
                          (Term.str_of rank));
                  Map.Poly.add_exn lexmap ~key:(pred.name, j, 0) ~data:rank)
            in
            Debug.print @@ lazy "*************************************";
            loop param_constrs' lexmap' (j + 1)
        | Ok None -> None
        | Error err -> failwith (Error.to_string_hum err))
      else Some lexmap
    in
    loop param_constrs Map.Poly.empty 1

  let synthesize_lexgssm (qfl : QFL.Problem.t)
      (init, invmap, param_senv, param_constrs) =
    let d_div_2 = div_ceil (QFL.Problem.depth_of qfl) 2 in
    let rec loop param_constrs lexmap j =
      if j <= d_div_2 then (
        let preds =
          Set.filter (Set.Poly.of_list qfl.preds) ~f:(fun pred ->
              QFL.Problem.level_of qfl pred.name >= (2 * j) - 1)
        in
        Debug.print ~id:None
        @@ lazy
             (sprintf "\n***synthesizing ranking supermartingales at level %d\n"
                j);
        let rec inner param_constrs lexmap (preds : QFL.Pred.t Set.Poly.t) k =
          let param_constrs', lexmap', elimed =
            let inv_templ_paramss, inv_templ_preds =
              gen_inv_templ init param_senv qfl.preds
            in
            let inv_sub = Map.Poly.of_alist_exn inv_templ_preds in
            let rank_templ_paramss, rank_templ_preds =
              gen_rank_templ param_senv qfl.preds
            in
            let rank_sub = Map.Poly.of_alist_exn rank_templ_preds in
            let pred_eps_set =
              Set.Poly.map preds ~f:(fun pred ->
                  let eps = Ident.mk_fresh_tvar ~prefix:(Some "eps") () in
                  Debug.print
                  @@ lazy
                       (sprintf "%s |-> %s"
                          (Ident.name_of_tvar pred.name)
                          (Ident.name_of_tvar eps));
                  (pred, eps))
            in
            let constrs_inv = gen_inv_constrs init inv_sub invmap qfl.preds in
            let constrs_rank =
              Formula.geq
                (T_real.mk_rsum (T_real.rzero ())
                @@ Set.to_list
                @@ Set.Poly.map pred_eps_set ~f:(fun (_, eps) ->
                    Term.mk_var eps T_real.SReal))
                (T_real.rone ())
              :: (Set.to_list
                 @@ Set.concat_map pred_eps_set ~f:(fun (_, eps) ->
                     Set.Poly.of_list
                     @@ Formula.mk_range_real
                          (Term.mk_var eps T_real.SReal)
                          Q.zero Q.one))
              @ gen_rank_constrs inv_sub invmap pred_eps_set rank_sub
                  rank_templ_preds
            in
            let constrs =
              Set.to_list param_constrs @ constrs_inv @ constrs_rank
            in
            let templ_params =
              Map.force_merge_list
              @@ Map.Poly.of_alist_exn param_senv
                 :: (Map.of_set_exn
                    @@ Set.Poly.map pred_eps_set ~f:(fun (_, eps) ->
                        (eps, T_real.SReal)))
                 :: rank_templ_paramss
              @ List.map ~f:Logic.to_old_sort_env_map inv_templ_paramss
            in
            match solve_constrs templ_params constrs with
            | Ok (Some model) ->
                let tsub =
                  Logic.ExtTerm.to_old_subst Map.Poly.empty Map.Poly.empty model
                in
                let param_constrs' = conv tsub param_senv constrs in
                Debug.print @@ lazy "*************************************";
                List.iter inv_templ_preds ~f:(fun (name, (args, pred)) ->
                    let inv = Evaluator.simplify @@ Formula.subst tsub pred in
                    Debug.print
                    @@ lazy
                         (sprintf "synthesized invariant for %s: %s |-> %s"
                            (Ident.name_of_tvar name)
                            (str_of_sort_env_list Term.str_of_sort args)
                            (Formula.str_of inv)));
                Debug.print @@ lazy "*************************************";
                let lexmap', elimed =
                  let ranks =
                    List.map rank_templ_preds
                      ~f:(fun (name, (args, quant_pred)) ->
                        ( name,
                          ( args,
                            Evaluator.simplify_term
                            @@ Term.subst tsub quant_pred ) ))
                  in
                  List.fold ~init:(lexmap, Set.Poly.empty) qfl.preds
                    ~f:(fun (lexmap, elimed) pred ->
                      let rank, elimed =
                        let rank_args, rank_body =
                          List.Assoc.find_exn ~equal:Stdlib.( = ) ranks
                            pred.name
                        in
                        let rank =
                          Term.rename
                            (LogicOld.ren_of_sort_env_list rank_args pred.args)
                            rank_body
                        in
                        match
                          Set.find pred_eps_set ~f:(fun (p, _) ->
                              Stdlib.( = ) p pred)
                        with
                        | None -> (rank, elimed)
                        | Some (_, eps) ->
                            let eps =
                              T_real.let_real
                              @@ Term.subst tsub (Term.mk_var eps T_real.SReal)
                            in
                            if Q.gt eps Q.zero then
                              let rank =
                                Evaluator.simplify_term
                                @@ Normalizer.normalize_term
                                @@ T_real.mk_rmul
                                     (T_real.mk_real Q.(one / eps))
                                     rank
                              in
                              (rank, Set.add elimed pred.name)
                            else (rank, elimed)
                      in
                      Debug.print
                      @@ lazy
                           (sprintf
                              "synthesized ranking supermartingale for (%s, \
                               %d, %d): %s |-> %s"
                              (Ident.name_of_tvar pred.name)
                              j k
                              (str_of_sort_env_list Term.str_of_sort pred.args)
                              (Term.str_of rank));
                      ( Map.Poly.add_exn lexmap ~key:(pred.name, j, k) ~data:rank,
                        elimed ))
                in
                Debug.print @@ lazy "*************************************";
                (param_constrs', lexmap', elimed)
            | Ok None ->
                ( param_constrs,
                  List.fold ~init:lexmap qfl.preds ~f:(fun lexmap pred ->
                      let rank = T_real.rzero () in
                      Debug.print
                      @@ lazy
                           (sprintf
                              "synthesized ranking supermartingale for (%s, \
                               %d, %d): %s |-> %s"
                              (Ident.name_of_tvar pred.name)
                              j k
                              (str_of_sort_env_list Term.str_of_sort pred.args)
                              (Term.str_of rank));
                      Map.Poly.add_exn lexmap ~key:(pred.name, j, k) ~data:rank),
                  Set.Poly.empty )
            | Error err -> failwith (Error.to_string_hum err)
          in
          if Set.is_empty elimed then (param_constrs', lexmap', preds)
          else
            let preds' =
              Set.filter preds ~f:(fun pred -> not @@ Set.mem elimed pred.name)
            in
            inner param_constrs' lexmap' preds' (k + 1)
        in
        let param_constrs, lexmap, preds = inner param_constrs lexmap preds 0 in
        if
          Set.exists preds ~f:(fun pred ->
              QFL.Problem.level_of qfl pred.name = (2 * j) - 1)
        then None
        else loop param_constrs lexmap (j + 1))
      else Some lexmap
    in
    loop param_constrs Map.Poly.empty 1

  let synthesize_pmsm (qfl : QFL.Problem.t)
      (init, invmap, param_senv, param_constrs) =
    let d_div_2 = div_ceil (QFL.Problem.depth_of qfl) 2 in
    let rec loop param_constrs lexmap (preds : QFL.Pred.t Set.Poly.t) j =
      if j <= d_div_2 then (
        let preds =
          Set.filter preds ~f:(fun pred ->
              QFL.Problem.level_of qfl pred.name >= (2 * j) - 1)
        in
        Debug.print ~id:None
        @@ lazy
             (sprintf "\n***synthesizing ranking supermartingales at level %d\n"
                j);
        let inv_templ_paramss, inv_templ_preds =
          gen_inv_templ init param_senv qfl.preds
        in
        let inv_sub = Map.Poly.of_alist_exn inv_templ_preds in
        let rank_templ_paramss, rank_templ_preds =
          gen_rank_templ param_senv qfl.preds
        in
        let rank_sub = Map.Poly.of_alist_exn rank_templ_preds in
        let pred_eps_set =
          Set.Poly.map preds ~f:(fun pred ->
              let eps = Ident.mk_fresh_tvar ~prefix:(Some "eps") () in
              Debug.print
              @@ lazy
                   (sprintf "%s |-> %s"
                      (Ident.name_of_tvar pred.name)
                      (Ident.name_of_tvar eps));
              (pred, eps))
        in
        let constrs_inv = gen_inv_constrs init inv_sub invmap qfl.preds in
        let constrs_rank =
          (Set.to_list
          @@ Set.concat_map pred_eps_set ~f:(fun (pred, eps) ->
              if QFL.Problem.level_of qfl pred.name = (2 * j) - 1 then
                Set.Poly.singleton
                @@ Formula.eq (Term.mk_var eps T_real.SReal) (T_real.rone ())
              else
                Set.Poly.of_list
                @@ Formula.mk_range_real
                     (Term.mk_var eps T_real.SReal)
                     Q.zero Q.one))
          @ gen_rank_constrs inv_sub invmap pred_eps_set rank_sub
              rank_templ_preds
        in
        let constrs = Set.to_list param_constrs @ constrs_inv @ constrs_rank in
        let templ_params =
          Map.force_merge_list
          @@ Map.Poly.of_alist_exn param_senv
             :: (Map.of_set_exn
                @@ Set.Poly.map pred_eps_set ~f:(fun (_, eps) ->
                    (eps, T_real.SReal)))
             :: rank_templ_paramss
          @ List.map ~f:Logic.to_old_sort_env_map inv_templ_paramss
        in
        match solve_constrs templ_params constrs with
        | Ok (Some model) ->
            let tsub =
              Logic.ExtTerm.to_old_subst Map.Poly.empty Map.Poly.empty model
            in
            let param_constrs' = conv tsub param_senv constrs in
            Debug.print @@ lazy "*************************************";
            List.iter inv_templ_preds ~f:(fun (name, (args, pred)) ->
                let inv = Evaluator.simplify @@ Formula.subst tsub pred in
                Debug.print
                @@ lazy
                     (sprintf "synthesized invariant for %s: %s |-> %s"
                        (Ident.name_of_tvar name)
                        (str_of_sort_env_list Term.str_of_sort args)
                        (Formula.str_of inv)));
            Debug.print @@ lazy "*************************************";
            let lexmap', elimed =
              let ranks =
                List.map rank_templ_preds ~f:(fun (name, (args, quant_pred)) ->
                    ( name,
                      ( args,
                        Evaluator.simplify_term @@ Term.subst tsub quant_pred )
                    ))
              in
              List.fold ~init:(lexmap, Set.Poly.empty) qfl.preds
                ~f:(fun (lexmap, elimed) pred ->
                  let rank, elimed =
                    let rank_args, rank_body =
                      List.Assoc.find_exn ~equal:Stdlib.( = ) ranks pred.name
                    in
                    let rank =
                      Term.rename
                        (LogicOld.ren_of_sort_env_list rank_args pred.args)
                        rank_body
                    in
                    match
                      Set.find pred_eps_set ~f:(fun (p, _) ->
                          Stdlib.( = ) p pred)
                    with
                    | None -> (rank, elimed)
                    | Some (_, eps) ->
                        let eps =
                          T_real.let_real
                          @@ Term.subst tsub (Term.mk_var eps T_real.SReal)
                        in
                        if Q.gt eps Q.zero then
                          let rank =
                            Evaluator.simplify_term @@ Normalizer.normalize_term
                            @@ T_real.mk_rmul
                                 (T_real.mk_real Q.(one / eps))
                                 rank
                          in
                          (rank, Set.add elimed pred.name)
                        else (rank, elimed)
                  in
                  Debug.print
                  @@ lazy
                       (sprintf
                          "synthesized ranking supermartingale for (%s, %d, \
                           %d): %s |-> %s"
                          (Ident.name_of_tvar pred.name)
                          j 0
                          (str_of_sort_env_list Term.str_of_sort pred.args)
                          (Term.str_of rank));
                  ( Map.Poly.add_exn lexmap ~key:(pred.name, j, 0) ~data:rank,
                    elimed ))
            in
            Debug.print @@ lazy "*************************************";
            let preds' =
              Set.filter preds ~f:(fun pred -> not @@ Set.mem elimed pred.name)
            in
            loop param_constrs' lexmap' preds' (j + 1)
        | Ok None -> None
        | Error err -> failwith (Error.to_string_hum err))
      else Some lexmap
    in
    loop param_constrs Map.Poly.empty (Set.Poly.of_list qfl.preds) 1

  let synthesize_lexpmsm (qfl : QFL.Problem.t)
      (init, invmap, param_senv, param_constrs) =
    let d_div_2 = div_ceil (QFL.Problem.depth_of qfl) 2 in
    let rec loop param_constrs lexmap (preds : QFL.Pred.t Set.Poly.t) j =
      if j <= d_div_2 then (
        let preds =
          Set.filter preds ~f:(fun pred ->
              QFL.Problem.level_of qfl pred.name >= (2 * j) - 1)
        in
        Debug.print ~id:None
        @@ lazy
             (sprintf "\n***synthesizing ranking supermartingales at level %d\n"
                j);
        let rec inner param_constrs lexmap (preds : QFL.Pred.t Set.Poly.t) k =
          let param_constrs', lexmap', elimed =
            let inv_templ_paramss, inv_templ_preds =
              gen_inv_templ init param_senv qfl.preds
            in
            let inv_sub = Map.Poly.of_alist_exn inv_templ_preds in
            let rank_templ_paramss, rank_templ_preds =
              gen_rank_templ param_senv qfl.preds
            in
            let rank_sub = Map.Poly.of_alist_exn rank_templ_preds in
            let pred_eps_set =
              Set.Poly.map preds ~f:(fun pred ->
                  let eps = Ident.mk_fresh_tvar ~prefix:(Some "eps") () in
                  Debug.print
                  @@ lazy
                       (sprintf "%s |-> %s"
                          (Ident.name_of_tvar pred.name)
                          (Ident.name_of_tvar eps));
                  (pred, eps))
            in
            let constrs_inv = gen_inv_constrs init inv_sub invmap qfl.preds in
            let constrs_rank =
              Formula.geq
                (T_real.mk_rsum (T_real.rzero ())
                @@ Set.to_list
                @@ Set.Poly.map pred_eps_set ~f:(fun (_, eps) ->
                    Term.mk_var eps T_real.SReal))
                (T_real.rone ())
              :: (Set.to_list
                 @@ Set.concat_map pred_eps_set ~f:(fun (_, eps) ->
                     Set.Poly.of_list
                     @@ Formula.mk_range_real
                          (Term.mk_var eps T_real.SReal)
                          Q.zero Q.one))
              @ gen_rank_constrs inv_sub invmap pred_eps_set rank_sub
                  rank_templ_preds
            in
            let constrs =
              Set.to_list param_constrs @ constrs_inv @ constrs_rank
            in
            let templ_params =
              Map.force_merge_list
              @@ Map.Poly.of_alist_exn param_senv
                 :: (Map.of_set_exn
                    @@ Set.Poly.map pred_eps_set ~f:(fun (_, eps) ->
                        (eps, T_real.SReal)))
                 :: rank_templ_paramss
              @ List.map ~f:Logic.to_old_sort_env_map inv_templ_paramss
            in
            match solve_constrs templ_params constrs with
            | Ok (Some model) ->
                let tsub =
                  Logic.ExtTerm.to_old_subst Map.Poly.empty Map.Poly.empty model
                in
                let param_constrs' = conv tsub param_senv constrs in
                Debug.print @@ lazy "*************************************";
                List.iter inv_templ_preds ~f:(fun (name, (args, pred)) ->
                    let inv = Evaluator.simplify @@ Formula.subst tsub pred in
                    Debug.print
                    @@ lazy
                         (sprintf "synthesized invariant for %s: %s |-> %s"
                            (Ident.name_of_tvar name)
                            (str_of_sort_env_list Term.str_of_sort args)
                            (Formula.str_of inv)));
                Debug.print @@ lazy "*************************************";
                let lexmap', elimed =
                  let ranks =
                    List.map rank_templ_preds
                      ~f:(fun (name, (args, quant_pred)) ->
                        ( name,
                          ( args,
                            Evaluator.simplify_term
                            @@ Term.subst tsub quant_pred ) ))
                  in
                  List.fold ~init:(lexmap, Set.Poly.empty) qfl.preds
                    ~f:(fun (lexmap, elimed) pred ->
                      let rank, elimed =
                        let rank_args, rank_body =
                          List.Assoc.find_exn ~equal:Stdlib.( = ) ranks
                            pred.name
                        in
                        let rank =
                          Term.rename
                            (LogicOld.ren_of_sort_env_list rank_args pred.args)
                            rank_body
                        in
                        match
                          Set.find pred_eps_set ~f:(fun (p, _) ->
                              Stdlib.( = ) p pred)
                        with
                        | None -> (rank, elimed)
                        | Some (_, eps) ->
                            let eps =
                              T_real.let_real
                              @@ Term.subst tsub (Term.mk_var eps T_real.SReal)
                            in
                            if Q.gt eps Q.zero then
                              let rank =
                                Evaluator.simplify_term
                                @@ Normalizer.normalize_term
                                @@ T_real.mk_rmul
                                     (T_real.mk_real Q.(one / eps))
                                     rank
                              in
                              (rank, Set.add elimed pred.name)
                            else (rank, elimed)
                      in
                      Debug.print
                      @@ lazy
                           (sprintf
                              "synthesized ranking supermartingale for (%s, \
                               %d, %d): %s |-> %s"
                              (Ident.name_of_tvar pred.name)
                              j k
                              (str_of_sort_env_list Term.str_of_sort pred.args)
                              (Term.str_of rank));
                      ( Map.Poly.add_exn lexmap ~key:(pred.name, j, k) ~data:rank,
                        elimed ))
                in
                Debug.print @@ lazy "*************************************";
                (param_constrs', lexmap', elimed)
            | Ok None ->
                ( param_constrs,
                  List.fold ~init:lexmap qfl.preds ~f:(fun lexmap pred ->
                      let rank = T_real.rzero () in
                      Debug.print
                      @@ lazy
                           (sprintf
                              "synthesized ranking supermartingale for (%s, \
                               %d, %d): %s |-> %s"
                              (Ident.name_of_tvar pred.name)
                              j k
                              (str_of_sort_env_list Term.str_of_sort pred.args)
                              (Term.str_of rank));
                      Map.Poly.add_exn lexmap ~key:(pred.name, j, k) ~data:rank),
                  Set.Poly.empty )
            | Error err -> failwith (Error.to_string_hum err)
          in
          if Set.is_empty elimed then (param_constrs', lexmap', preds)
          else
            let preds' =
              Set.filter preds ~f:(fun pred -> not @@ Set.mem elimed pred.name)
            in
            inner param_constrs' lexmap' preds' (k + 1)
        in
        let param_constrs, lexmap, preds = inner param_constrs lexmap preds 0 in
        if
          Set.exists preds ~f:(fun pred ->
              QFL.Problem.level_of qfl pred.name = (2 * j) - 1)
        then None
        else loop param_constrs lexmap preds (j + 1))
      else Some lexmap
    in
    loop param_constrs Map.Poly.empty (Set.Poly.of_list qfl.preds) 1

  let synthesize_invs (qfl : QFL.Problem.t) (init, param_senv, param_constrs) =
    match init with
    | None -> (init, Map.Poly.empty, param_senv, param_constrs)
    | Some _ ->
        let inv_templ_paramss, inv_templ_preds =
          gen_inv_templ init param_senv qfl.preds
        in
        let inv_sub = Map.Poly.of_alist_exn inv_templ_preds in
        let rec loop cnt invmap freshness_constrs param_constrs =
          let constrs_inv = gen_inv_constrs init inv_sub invmap qfl.preds in
          let constrs =
            Set.to_list param_constrs
            @ Set.to_list freshness_constrs
            @ constrs_inv
          in
          let templ_params =
            Map.force_merge_list
            @@ Map.Poly.of_alist_exn param_senv
               :: List.map ~f:Logic.to_old_sort_env_map inv_templ_paramss
          in
          match solve_constrs templ_params constrs with
          | Ok (Some model) ->
              let tsub =
                Logic.ExtTerm.to_old_subst Map.Poly.empty Map.Poly.empty model
              in
              if false then print_endline @@ TermSubst.str_of tsub;
              let rat =
                List.map inv_templ_paramss ~f:(fun m ->
                    ( m,
                      Term.mk_var
                        (Ident.mk_fresh_tvar ~prefix:(Some "r_") ())
                        T_real.SReal ))
              in
              let freshness_constrs' =
                Set.add freshness_constrs
                  (Formula.mk_imply
                     (Formula.and_of
                        (Map.Poly.fold model
                           ~init:
                             (List.map rat ~f:(fun (_, r) ->
                                  Formula.mk_atom
                                  @@ T_real.mk_rgt r (T_real.rzero ())))
                           ~f:(fun ~key ~data eqs ->
                             if
                               List.Assoc.mem ~equal:Stdlib.( = ) param_senv key
                             then eqs
                             else
                               let _, r =
                                 List.find_exn rat ~f:(fun (m, _) ->
                                     Map.Poly.mem m key)
                               in
                               Formula.eq
                                 (Term.mk_var key T_real.SReal)
                                 (T_real.mk_rmul
                                    (Logic.ExtTerm.to_old_trm Map.Poly.empty
                                       Map.Poly.empty data)
                                    r)
                               :: eqs)))
                     (Formula.mk_false ()))
              in
              let param_constrs' = conv tsub param_senv constrs in
              Debug.print @@ lazy "*************************************";
              let invmap' =
                List.fold ~init:invmap inv_templ_preds
                  ~f:(fun invmap (name, (args, pred)) ->
                    let inv = Evaluator.simplify @@ Formula.subst tsub pred in
                    match Map.Poly.find invmap name with
                    | None ->
                        Debug.print
                        @@ lazy
                             (sprintf "synthesized invariant for %s: %s |-> %s"
                                (Ident.name_of_tvar name)
                                (str_of_sort_env_list Term.str_of_sort args)
                                (Formula.str_of inv));
                        if Formula.is_true inv then invmap
                        else Map.Poly.add_exn invmap ~key:name ~data:(args, inv)
                    | Some (args', inv') ->
                        let inv'' =
                          Evaluator.simplify
                          @@ Formula.and_of
                               [
                                 inv';
                                 Formula.rename
                                   (LogicOld.ren_of_sort_env_list args args')
                                   inv;
                               ]
                        in
                        Debug.print
                        @@ lazy
                             (sprintf "synthesized invariant for %s: %s |-> %s"
                                (Ident.name_of_tvar name)
                                (str_of_sort_env_list Term.str_of_sort args)
                                (Formula.str_of inv''));
                        Map.Poly.set invmap ~key:name ~data:(args', inv''))
              in
              Debug.print @@ lazy "*************************************";
              if cnt <= 4 (*ToDo*) then
                loop (cnt + 1) invmap' freshness_constrs' param_constrs'
              else (init, invmap', param_senv, param_constrs')
          | Ok None -> (init, invmap, param_senv, param_constrs)
          | Error err -> failwith (Error.to_string_hum err)
        in
        let freshness_constrs =
          Set.Poly.singleton
          @@ Formula.mk_imply
               (Formula.and_of
                  (Set.to_list
                  @@ Set.Poly.map
                       (Set.Poly.union_list
                       @@ List.map ~f:Map.Poly.key_set inv_templ_paramss)
                       ~f:(fun x ->
                         Formula.eq
                           (Term.mk_var x T_real.SReal)
                           (T_real.rzero ()))))
               (Formula.mk_false ())
        in
        loop 0 Map.Poly.empty freshness_constrs param_constrs

  let synthesize_omega_regular_supermartingale qfl
      (init, param_senv, param_constrs) =
    (match config.quant_omega_regular_supermartingale with
      | SSM -> synthesize_ssm qfl
      | GSSM -> synthesize_gssm qfl
      | LexGSSM -> synthesize_lexgssm qfl
      | PMSM -> synthesize_pmsm qfl
      | LexPMSM -> synthesize_lexpmsm qfl)
    @@
    if simul_inv_syn then (init, Map.Poly.empty, param_senv, param_constrs)
    else synthesize_invs qfl (None, param_senv, param_constrs)

  let check_almost_sure_satisfaction_of_omega_regular_properties
      ?(print_sol = false) (qfl : QFL.Problem.t)
      (init, param_senv, param_constrs) =
    match
      synthesize_omega_regular_supermartingale qfl
        (init, param_senv, param_constrs)
    with
    | None ->
        if print_sol then print_endline @@ sprintf "unknown";
        Or_error.return ([], [])
    | Some _ ->
        if print_sol then print_endline @@ sprintf "sat";
        Or_error.return ([], [])

  let check_bounds ~print_sol (i, sols, pareto_cache) qfl
      (query : QFL.Problem.check) =
    Timer.start ();
    if not @@ QFL.Problem.has_only_mu qfl then failwith "GFPs not supported";
    let fsub, qfl = QFL.Problem.unfold qfl in
    Debug.print ~id:None
    @@ lazy (sprintf "inlined: %s\n" @@ QFL.Problem.str_of ~fsub:(Some fsub) qfl);
    let ((ua_preds, prefp, rank, postfp), pqes), backup =
      let query_fml =
        Formula.subst_funcs fsub @@ QFL.Problem.formula_of_query (Check query)
      in
      match query.kind with
      | LB -> cgen_pqes_lb qfl query_fml fsub pareto_cache
      | UB -> cgen_pqes_ub qfl query_fml fsub pareto_cache
    in
    let timeout =
      match backup with None -> None | Some _ -> config.pareto_cache_timeout
    in
    Debug.print ~id:None
    @@ lazy (sprintf "******* Generated PQEs:\n%s" @@ PCSP.Problem.str_of pqes);
    let open Or_error.Monad_infix in
    pcsp_solver ~primal:true >>= fun (module PCSPSolver) ->
    pcsp_solver ~primal:false >>= fun (module PCSPSolverPC) ->
    ( (match backup with
      | None -> PCSPSolver.solve
      | Some _ -> PCSPSolverPC.solve)
        ~timeout pqes
    >>= function
      | PCSP.Problem.Sat model, info ->
          let tsub =
            Logic.ExtTerm.to_old_subst Map.Poly.empty Map.Poly.empty model
          in
          let prefp =
            List.map prefp ~f:(fun (name, (args, quant_pred)) ->
                ( name,
                  (args, Evaluator.simplify_term @@ Term.subst tsub quant_pred)
                ))
          in
          let rank =
            List.map rank ~f:(fun (name, (args, quant_pred)) ->
                ( name,
                  (args, Evaluator.simplify_term @@ Term.subst tsub quant_pred)
                ))
          in
          let postfp =
            List.map postfp ~f:(fun (name, (args, quant_pred)) ->
                ( name,
                  (args, Evaluator.simplify_term @@ Term.subst tsub quant_pred)
                ))
          in
          (match ua_preds with
          | None -> ()
          | Some ua_preds ->
              let ua_preds =
                List.map ua_preds ~f:(fun pred ->
                    { pred with body = Term.subst tsub pred.body })
              in
              Debug.print ~id:None
              @@ lazy
                   (sprintf "\nunderapproximated:\n%s"
                   @@ QFL.Pred.str_of_list ua_preds));
          if not @@ List.is_empty prefp then (
            Debug.print @@ lazy "\nsynthesized prefixpoint:";
            print_templ prefp);
          if not @@ List.is_empty rank then (
            Debug.print @@ lazy "\nsynthesized ranking supermartingales:";
            print_templ rank);
          if not @@ List.is_empty postfp then (
            Debug.print @@ lazy "\nsynthesized postfixpoint:";
            print_templ postfp);
          Ok
            ( MuCLP.Problem.Valid,
              Some (match query.kind with LB -> postfp | UB -> prefp),
              info )
      | Unsat _, info ->
          Debug.print @@ lazy "the templates used may not be expressive enough";
          Ok (Unknown, None, info)
      | Unknown, info ->
          Debug.print
          @@ lazy
               "the backend PQE solver failed or the templates used may not be \
                expressive enough";
          Ok (Unknown, None, info)
      | OutSpace _, _ -> failwith "out of space" (* TODO *)
      | Timeout, info -> Ok (Timeout, None, info) )
    >>= function
    | (MuCLP.Problem.Valid as sol), Some fp, info ->
        let time = Timer.stop () in
        Debug.print @@ lazy "=========================";
        let fp =
          fp
          @ List.map (Map.Poly.to_alist fsub)
              ~f:(fun (name, (args, quant_pred)) ->
                ( name,
                  (args, Term.subst_funcs (Map.Poly.of_alist_exn fp) quant_pred)
                ))
        in
        if print_sol then
          print_endline @@ String.concat ~sep:", "
          @@ MuCLP.Problem.(
               if config.output_yes_no then lts_str_of_solution
               else str_of_solution)
               sol
             :: (if config.output_iteration then [ sprintf "%d" info ] else [])
          @ (if config.output_time then
               [
                 (match backup with
                 | Some _ -> sprintf "%fs (cache)" time
                 | None -> sprintf "%fs" time);
               ]
             else [])
          @ if config.output_witness then [ str_of_templ fp ] else [];
        Or_error.return
          ( sols @ [ sol ],
            pareto_cache
            @ [ (match backup with None -> Some fp | Some _ -> None) ] )
    | _ -> (
        match backup with
        | None ->
            Or_error.error_string
              ("failed to solve Problem " ^ string_of_int (i + 1))
        | Some ((ua_preds, prefp, rank, postfp), pqes) -> (
            Debug.print @@ lazy "\npareto cache did not help, try backup";
            Debug.print ~id:None
            @@ lazy
                 (sprintf "******* Generated PQEs:\n%s"
                 @@ PCSP.Problem.str_of pqes);
            let open Or_error.Monad_infix in
            pcsp_solver ~primal:true >>= fun (module PCSPSolver) ->
            ( PCSPSolver.solve pqes >>= function
              | PCSP.Problem.Sat model, info ->
                  let tsub =
                    Logic.ExtTerm.to_old_subst Map.Poly.empty Map.Poly.empty
                      model
                  in
                  let prefp =
                    List.map prefp ~f:(fun (name, (args, quant_pred)) ->
                        ( name,
                          ( args,
                            Evaluator.simplify_term
                            @@ Term.subst tsub quant_pred ) ))
                  in
                  let rank =
                    List.map rank ~f:(fun (name, (args, quant_pred)) ->
                        ( name,
                          ( args,
                            Evaluator.simplify_term
                            @@ Term.subst tsub quant_pred ) ))
                  in
                  let postfp =
                    List.map postfp ~f:(fun (name, (args, quant_pred)) ->
                        ( name,
                          ( args,
                            Evaluator.simplify_term
                            @@ Term.subst tsub quant_pred ) ))
                  in
                  (match ua_preds with
                  | None -> ()
                  | Some ua_preds ->
                      let ua_preds =
                        List.map ua_preds ~f:(fun (pred : QFL.Pred.t) ->
                            { pred with body = Term.subst tsub pred.body })
                      in
                      Debug.print ~id:None
                      @@ lazy
                           (sprintf "\nunderapproximated:\n%s"
                           @@ QFL.Pred.str_of_list ua_preds));
                  if not @@ List.is_empty prefp then (
                    Debug.print @@ lazy "\nsynthesized prefixpoint:";
                    print_templ prefp);
                  if not @@ List.is_empty rank then (
                    Debug.print
                    @@ lazy "\nsynthesized ranking supermartingales:";
                    print_templ rank);
                  if not @@ List.is_empty postfp then (
                    Debug.print @@ lazy "\nsynthesized postfixpoint:";
                    print_templ postfp);
                  Ok
                    ( MuCLP.Problem.Valid,
                      Some (match query.kind with LB -> postfp | UB -> prefp),
                      info )
              | Unsat _, info ->
                  Debug.print
                  @@ lazy "the templates used may not be expressive enough";
                  Ok (Unknown, None, info)
              | Unknown, info ->
                  Debug.print
                  @@ lazy
                       "the backend PQE solver failed or the templates used \
                        may not be expressive enough";
                  Ok (Unknown, None, info)
              | OutSpace _, _ -> failwith "out of space" (* TODO *)
              | Timeout, info -> Ok (Timeout, None, info) )
            >>= function
            | (MuCLP.Problem.Valid as sol), Some fp, info ->
                let time = Timer.stop () in
                Debug.print @@ lazy "=========================";
                let fp =
                  fp
                  @ List.map (Map.Poly.to_alist fsub)
                      ~f:(fun (name, (args, quant_pred)) ->
                        ( name,
                          ( args,
                            Term.subst_funcs (Map.Poly.of_alist_exn fp)
                              quant_pred ) ))
                in
                if print_sol then
                  print_endline @@ String.concat ~sep:", "
                  @@ MuCLP.Problem.(
                       if config.output_yes_no then lts_str_of_solution
                       else str_of_solution)
                       sol
                     ::
                     (if config.output_iteration then [ sprintf "%d" info ]
                      else [])
                  @ (if config.output_time then [ sprintf "%fs" time ] else [])
                  @ if config.output_witness then [ str_of_templ fp ] else [];
                Or_error.return (sols @ [ sol ], pareto_cache @ [ Some fp ])
            | _ ->
                Or_error.error_string
                  ("failed to solve Problem " ^ string_of_int (i + 1))))

  let check_dist_bounds ~print_sol qfl (q : QFL.Problem.dist_check) =
    let check ?(strict = false) bound sub =
      let query : QFL.Problem.check =
        {
          params = [];
          left = None;
          kind = UB;
          name = q.name;
          args = q.args;
          bound;
          strict;
        }
      in
      let qfl =
        let sub =
          Map.Poly.of_alist_exn
            (List.map sub ~f:(fun (x, v) -> (x, T_real.mk_real v)))
        in
        QFL.Problem.
          {
            preds = List.map qfl.preds ~f:(QFL.Pred.subst sub);
            query = Check query;
          }
      in
      Debug.print ~id:None
      @@ lazy (sprintf "\ninput: %s\n" @@ QFL.Problem.str_of qfl);
      match check_bounds ~print_sol (-1, [], []) qfl query with
      | Ok (_, [ Some sol ]) ->
          let senv, t = List.Assoc.find_exn ~equal:Stdlib.( = ) sol q.name in
          let bound =
            Value.real_of @@ Evaluator.eval_term
            @@ Term.subst
                 (Map.Poly.of_alist_exn
                 @@ List.map2_exn senv q.args ~f:(fun (x, _) t -> (x, t)))
                 t
          in
          Debug.print @@ lazy (sprintf "found bound: %s\n" (Q.to_string bound));
          (List.map sub ~f:snd, bound)
      | _ -> failwith "failed to solve dist_check"
    in
    let h =
      let res =
        if Formula.is_atom q.bound then
          let atm, _ = Formula.let_atom q.bound in
          if Atom.is_psym_app atm then
            let op, args, _ = Atom.let_psym_app atm in
            match (op, args) with
            | T_real.RLeq, [ t; bound ] -> (
                try
                  let bound =
                    match Evaluator.eval_term bound with
                    | Value.Real r -> r
                    | _ -> failwith "unexpected"
                  in
                  let monomials =
                    Normalizer.linear_real_monomials_of (Value.Real Q.one) t
                  in
                  let c0 =
                    match Map.Poly.find monomials None with
                    | Some const -> Value.real_of const
                    | None -> Q.zero
                  in
                  let b = Q.(bound - c0) in
                  let cs =
                    List.map q.params ~f:(fun (var, _) ->
                        match
                          Map.Poly.find monomials
                            (Some (Term.mk_var var T_real.SReal))
                        with
                        | Some coeff -> Q.(Value.real_of coeff / b)
                        | None -> Q.zero)
                  in
                  Some cs
                with _ -> None)
            | _ -> None
          else None
        else None
      in
      match res with
      | None ->
          if config.dist_bound_initialize_standard_basis then
            List.map ~f:(check ((*ToDo*) T_real.rone ()))
            @@ List.init (List.length q.params) ~f:(fun i ->
                List.init (List.length q.params) ~f:(fun j ->
                    ( Ident.Tvar ("@" ^ string_of_int (j + 1)),
                      if i = j then Q.one else Q.zero )))
          else
            List.init (List.length q.params) ~f:(fun i ->
                ( List.init (List.length q.params) ~f:(fun j ->
                      if i = j then Q.one else Q.zero),
                  Q.one ))
      | Some ws ->
          [
            check (T_real.rone ())
            @@ List.mapi ws ~f:(fun i w ->
                (Ident.Tvar ("@" ^ string_of_int (i + 1)), w));
          ]
    in
    let generators_of h =
      let vs = List.map q.params ~f:fst in
      let vmap = MuCyc.ApronInterface.mk_varmap vs in
      let atoms =
        List.map ~f:Normalizer.normalize_atom
        @@ List.map vs ~f:(fun v ->
            T_real.mk_rleq (T_real.rzero ()) (Term.mk_var v T_real.SReal))
        @ List.map h ~f:(fun (ws, b) ->
            T_real.mk_rleq
              (T_real.mk_rsum (T_real.rzero ())
              @@ List.map2_exn ws vs ~f:(fun w v ->
                  T_real.mk_rmul (T_real.mk_real w) (Term.mk_var v T_real.SReal))
              )
              (T_real.mk_real b))
      in
      let polyhedron = MuCyc.ApronInterface.mk_real_polyhedron vmap atoms in
      let vertices = MuCyc.ApronInterface.mk_vertex polyhedron vmap in
      List.map vertices ~f:(fun vertex ->
          List.map vs ~f:(Map.Poly.find_exn vertex))
    in
    let refine h =
      let gens = generators_of h in
      Debug.print ~id:None
      @@ lazy
           (sprintf "generators: %s"
              (String.concat_map_list ~sep:", " gens ~f:(fun ps ->
                   sprintf "[%s]"
                     (String.concat_map_list ~sep:", " ps ~f:Term.str_of))));
      let eps, weight, bounds =
        List.fold gens
          ~init:
            ( Q.zero,
              List.init (List.length q.params) ~f:(fun _ -> Q.zero),
              [ (Q.one, config.dist_bound_use_strict_bound) ] )
          ~f:(fun (eps, weight, bounds) ps ->
            if
              let sub =
                Map.Poly.of_alist_exn
                @@ List.map2_exn q.params ps ~f:(fun param p -> (fst param, p))
              in
              Evaluator.eval (Formula.subst sub q.bound)
            then (
              Debug.print ~id:None
              @@ lazy
                   (sprintf "non-cex generator: [%s]"
                      (String.concat_map_list ~sep:", " ps ~f:Term.str_of));
              (eps, weight, bounds))
            else (
              Debug.print ~id:None
              @@ lazy
                   (sprintf "cex generator: [%s]"
                      (String.concat_map_list ~sep:", " ps ~f:Term.str_of));
              let qs =
                List.init (List.length q.params) ~f:(fun _ ->
                    Term.mk_var
                      (Ident.mk_fresh_tvar ~prefix:(Some "q_") ())
                      T_real.SReal)
              in
              let constrs =
                let sub =
                  Map.Poly.of_alist_exn
                  @@ List.map2_exn q.params qs ~f:(fun param q ->
                      (fst param, q))
                in
                Formula.subst sub q.bound
                :: Formula.leq
                     (T_real.mk_rsum (T_real.rzero ()) qs)
                     (T_real.rone ())
                :: List.map qs ~f:(fun q -> Formula.leq (T_real.rzero ()) q)
                @ List.map2_exn qs ps ~f:Formula.leq
              in
              let obj =
                let f =
                  if config.dist_bound_use_l1_norm then T_real.mk_rsub
                  else fun ?(info = Dummy) p q ->
                    let d = T_real.mk_rsub p q in
                    T_real.mk_rmul ~info d d
                in
                T_real.mk_rsum (T_real.rzero ()) (List.map2_exn ps qs ~f)
              in
              let fenv = Map.Poly.empty in
              match
                if config.dist_bound_use_optimathsat then
                  OptiMathSAT.Solver.minimize constrs obj
                else
                  Z3Smt.Z3interface.check_opt ~id:None fenv constrs ~max:false
                    obj
              with
              | Some (eps', _, model) ->
                  let sub =
                    Map.Poly.of_alist_exn
                    @@ List.map model ~f:(fun ((x, s), v) ->
                        let v =
                          match v with None -> Term.mk_dummy s | Some v -> v
                        in
                        if false then
                          print_endline
                          @@ sprintf "%s -> %s" (Ident.name_of_tvar x)
                               (Term.str_of v);
                        (x, v))
                  in
                  let eps' =
                    match eps' with
                    | Some eps' when false -> (
                        match Evaluator.eval_term eps' with
                        | Value.Real eps' -> eps'
                        | Value.Int eps' -> Q.of_bigint eps'
                        | eps' -> failwith ("eps' = " ^ Value.str_of eps'))
                    | _ -> (
                        match Evaluator.eval_term (Term.subst sub obj) with
                        | Value.Real eps' -> eps'
                        | eps' -> failwith ("eps' = " ^ Value.str_of eps'))
                  in
                  let qs = List.map qs ~f:(Term.subst sub) in
                  if Q.(eps < eps') then
                    let ws = List.map2_exn ps qs ~f:T_real.mk_rsub in
                    let bound =
                      if config.dist_bound_use_l1_norm then Q.one
                      else
                        let q_w =
                          T_real.mk_rsum (T_real.rzero ())
                            (List.map2_exn qs ws ~f:T_real.mk_rmul)
                        in
                        match Evaluator.eval_term q_w with
                        | Value.Real q_w -> q_w
                        | q_w -> failwith ("q_w = " ^ Value.str_of q_w)
                    in
                    let bound =
                      match config.dist_bound_relax with
                      | None -> [ (bound, config.dist_bound_use_strict_bound) ]
                      | Some r ->
                          let bound' =
                            let p_w =
                              T_real.mk_rsum (T_real.rzero ())
                                (List.map2_exn ps ws ~f:T_real.mk_rmul)
                            in
                            match Evaluator.eval_term p_w with
                            | Value.Real p_w -> p_w
                            | p_w -> failwith ("p_w = " ^ Value.str_of p_w)
                          in
                          [
                            (bound, config.dist_bound_use_strict_bound);
                            (Q.(min (bound + of_float r) bound'), true);
                          ]
                    in
                    ( eps',
                      List.map ws ~f:(fun w ->
                          match Evaluator.eval_term w with
                          | Value.Real w -> w
                          | w -> failwith ("w = " ^ Value.str_of w)),
                      bound )
                  else (eps, weight, bounds)
              | None -> assert false))
      in
      if Q.(eps = zero) then None
      else (
        Debug.print ~id:None
        @@ lazy
             (sprintf
                "abstraction refinement with the new weight [%s] and upper \
                 bound %s"
                (String.concat_map_list ~sep:", " weight ~f:Q.to_string)
                (Q.to_string (fst @@ List.hd_exn bounds)));
        let sub =
          List.mapi weight ~f:(fun i w ->
              (Ident.Tvar ("@" ^ string_of_int (i + 1)), w))
        in
        let res =
          let rec loop = function
            | [] -> assert false
            | (bound, strict) :: bounds -> (
                try check ~strict (T_real.mk_real bound) sub
                with exn ->
                  if List.is_empty bounds then raise exn else loop bounds)
          in
          loop bounds
        in
        Some (res :: h))
    in
    let rec cegar h =
      match refine h with
      | None ->
          if print_sol then (
            print_endline (MuCLP.Problem.str_of_solution MuCLP.Problem.Valid);
            List.iter h ~f:(fun (ws, b) ->
                print_endline
                @@ sprintf "weight: [%s], bound: %s"
                     (String.concat_map_list ~sep:", " ws ~f:Q.to_string)
                     (Q.to_string b)));
          Ok ([], [])
      | Some h -> cegar h
    in
    let h = cegar h in
    match h with
    | Ok (_, _) -> Or_error.return ([], [])
    | Error err -> Or_error.error_string (Error.to_string_hum err)

  let solve_qfl ?(print_sol = false) (qfls : QFL.Problem.t list) =
    Debug.print @@ lazy "======== MuVal ========";
    List.foldi qfls
      ~init:(Or_error.return ([], []))
      ~f:(fun i res qfl ->
        Debug.print
        @@ lazy (sprintf "\n---- Problem %d/%d ----" (i + 1) (List.length qfls));
        let open Or_error in
        res >>= fun (sols, pareto_cache) ->
        Debug.print ~id:None
        @@ lazy (sprintf "input: %s\n" @@ QFL.Problem.str_of qfl);
        let qfl =
          if true (*ToDo*) then qfl
          else (* this may cause size explosion? *)
            let qfl = QFL.Problem.simplify qfl in
            Debug.print ~id:None
            @@ lazy (sprintf "simplified: %s\n" @@ QFL.Problem.str_of qfl);
            qfl
        in
        match qfl.query with
        | ASAT (init, param_senv, param_constr) ->
            check_almost_sure_satisfaction_of_omega_regular_properties
              ~print_sol qfl
              (init, param_senv, Formula.conjuncts_of param_constr)
        | Check query ->
            check_bounds ~print_sol (i, sols, pareto_cache) qfl query
        | DistCheck query -> check_dist_bounds ~print_sol qfl query)
end
