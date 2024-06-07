open Core
open Common
open Common.Ext
open Common.Util
open Ast
open Problem

module type SolverType = sig
  type solution = string * PCSP.Problem.solution * int

  val solve_all : ?print_sol:bool -> Problem.t list -> (unit, Error.t) Result.t
  val solve : ?print_sol:bool -> Problem.t -> (unit, Error.t) Result.t
  val solve_from_file : ?print_sol:bool -> string -> (unit, Error.t) Result.t
end

module Make (Config : Config.ConfigType) : SolverType = struct
  type solution = string * PCSP.Problem.solution * int

  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_module_name "RCaml"

  module Cgen = Cgen.Make (Config)

  let solver =
    let open Or_error in
    ExtFile.unwrap config.solver >>= fun cfg -> Ok (PCSPSolver.Solver.make cfg)

  let optimizer =
    let open Or_error in
    ExtFile.unwrap config.optimizer >>= fun cfg ->
    Ok (CHCOptSolver.Solver.make cfg)

  let solve_problem (info, problem) =
    let open Or_error.Monad_infix in
    match problem with
    | POptimization chcopt_problem ->
        optimizer >>= fun (module Optimizer : CHCOptSolver.Solver.SolverType) ->
        Ok (OptimizeSol (Optimizer.solve chcopt_problem))
    | PAssertion (preds, copreds, pcsp) ->
        Debug.print @@ lazy ("assert: " ^ info);
        solver >>= fun (module PCSPSolver : PCSPSolver.Solver.SolverType) ->
        let bpvs =
          Set.Poly.of_list
          @@ List.map ~f:Ident.pvar_to_tvar
          @@ Map.Poly.keys preds @ Map.Poly.keys copreds
        in
        let pcsp =
          let ren_ref = ref Map.Poly.empty in
          let pcsp =
            PCSP.Problem.map_if_raw_old pcsp ~f:(fun constrs ->
                let pren =
                  let pvs_preds =
                    Set.Poly.of_list @@ Map.Poly.(keys preds @ keys copreds)
                  in
                  let penv_dtrenv = Cgen.get_penv_dtrenv pvs_preds in
                  Cgen.pren_of penv_dtrenv pvs_preds
                  @@ Set.Poly.map ~f:snd constrs
                in
                ren_ref :=
                  Map.Poly.of_alist_exn
                  @@ List.map ~f:(fun ((name, _), pvar) ->
                         (Ident.Tvar name, Ident.pvar_to_tvar pvar))
                  @@ Map.Poly.to_alist pren;
                Set.Poly.map constrs ~f:(fun (senv, phi) ->
                    (senv, LogicOld.Formula.rename_sorted_pvars pren phi)))
          in
          (if config.cgen_config.instantiate_svars_to_int then
             PCSP.Problem.instantiate_svars_to_int
           else Fn.id)
          @@ PCSP.Problem.update_params pcsp
          @@
          let params = PCSP.Problem.params_of pcsp in
          {
            params with
            senv = Map.rename_keys_map !ren_ref params.senv;
            kind_map = Map.rename_keys_map !ren_ref params.kind_map;
          }
        in
        let timeout = config.timeout in
        PCSPSolver.solve ~timeout ~bpvs ~preds ~copreds pcsp
        >>= fun (solution, iter) ->
        Debug.print
        @@ lazy
             (sprintf "[ret] %s : %s, %d" info
                (PCSP.Problem.str_of_solution solution)
                iter);
        Debug.print @@ lazy "=============================================";
        Ok (AssertSol (info, solution, iter))

  let print_solution ?(print_sol = true) problem i = function
    | OptimizeSol (sol, iter) ->
        if print_sol then
          print_endline
          @@ CHCOpt.Problem.str_of_solution (Problem.senv_of problem) iter sol
    | AssertSol (str, solution, iter) ->
        (* (match solution with
           | PCSP.Problem.Sat term_map ->
            Map.Poly.iteri term_map ~f:(fun ~key ~data ->
               let open Ast in let open Logic in
               Debug.print @@ lazy
                 (sprintf "%s : %s" (Ident.name_of_tvar key) (ExtTerm.str_of data)))
           | _ -> ()); *)
        if print_sol then
          print_endline
          @@ sprintf "%s,%d   \t@assert %s [#%d] "
               (PCSP.Problem.str_of_solution solution)
               iter str (i + 1)

  let rec main_loop rets (problems : Problem.t list) =
    let open Or_error.Monad_infix in
    match problems with
    | problem :: problems' ->
        solve_problem problem >>= fun sol ->
        main_loop (rets @ [ sol ]) problems'
    | [] -> Ok rets

  let solve_all ?(print_sol = true) (problems : Problem.t list) =
    let open Or_error.Monad_infix in
    main_loop [] problems >>= fun sols ->
    List.iteri sols ~f:(fun i ->
        print_solution ~print_sol (List.nth_exn problems i) i);
    Ok ()

  let solve ?(print_sol = true) problem = solve_all ~print_sol [ problem ]

  let solve_from_file ?(print_sol = true) filename =
    match snd (Filename.split_extension filename) with
    | Some "ml" ->
        let open Or_error.Monad_infix in
        Cgen.from_ml_file config.cgen_config filename >>= solve_all ~print_sol
    | _ -> Or_error.unimplemented "solve_from_file"
end
