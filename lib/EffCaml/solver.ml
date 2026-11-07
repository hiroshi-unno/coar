(* EffCaml's entry point: verify an effectful OCaml program by higher-order
   model checking.

   [solve_from_file] accepts only a [.ml] file; [Cgen.from_ml_file] translates
   it into a list of named model-checking problems, and each is handed in turn
   to the configured [HOMCSolver], which prints its own verdict.  Every run
   prints a verdict: a problem the checker could not decide (an [Error], such
   as rules the checker rejects as ill-sorted or an automaton outside what it
   reads) prints [unknown] in place of its verdict and the remaining problems
   are still tried, and a translation that fails (an exception other than an
   asynchronous one) prints [unknown] for the file.  Either way the function
   then returns an [Error] naming the reason, which the command line prints as
   one line on standard error with a non-zero status, so a lost answer cannot
   pass for a run that had nothing to report.

   [solve_homc] verifies an EHMTT program (Unno, Tabuchi and Kobayashi,
   "Verification of tree-processing programs via higher-order model
   checking", APLAS 2010): it is reduced to HORS problems with a trivial tree
   automaton, each decided by the configured checker (whose wrapper
   translates it into the alternating dialect when that is HorSat2), under
   the options of [config.ehmtt].  A HORS problem given directly, of either
   automaton dialect, is handed to the configured checker as it is, the
   wrapper translating it when the checker reads the other dialect.  Either
   way the verdict is printed when [print_sol] holds. *)

open Core
open Common
open Common.Ext
open Common.Util

module type SolverType = sig
  val solve_from_file : ?print_sol:bool -> string -> (unit, Error.t) Result.t

  val solve_homc :
    ?print_sol:bool -> HOMC.Problem.t -> HOMC.Problem.solution Or_error.t
end

module Make (Config : Config.ConfigType) : SolverType = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let solver =
    let open Or_error in
    ExtFile.unwrap config.solver >>= fun cfg -> Ok (HOMCSolver.Solver.make cfg)

  let _ = Debug.set_module_name "EffCaml"

  module Cgen = Cgen.Make (Config)

  let solve_from_file ?(print_sol = true) filename =
    match snd (Filename.split_extension filename) with
    | Some "ml" -> (
        let open Or_error.Monad_infix in
        solver >>= fun (module HOMCSolver : HOMCSolver.Solver.SolverType) ->
        let unknown reason =
          if print_sol then print_endline "unknown";
          Or_error.error_string reason
        in
        let problems =
          try
            match config.cps_scheme with
            | Legacy -> Cgen.from_ml_file filename
            | Selective_atp ->
                CPS.Pipeline.from_ml_file ~verbose:config.verbose
                  ~mbcsol:config.mbcsol CPS.Pipeline.Selective_atp filename
          with exn_ when not (Common.Timer.is_async exn_) -> (
            match exn_ with
            | Common.Refusal.Refused msg -> Or_error.error_string msg
            | _ ->
                Or_error.error_string
                  ("EffCaml translation failed: " ^ Exn.to_string exn_))
        in
        match problems with
        | Error err -> unknown (Error.to_string_hum err)
        | Ok problems ->
            let failures =
              List.filter_map problems ~f:(fun (desc, prb) ->
                  Debug.print @@ lazy (sprintf "begin checking %s" desc);
                  let res =
                    match
                      try HOMCSolver.solve ~print_sol prb
                      with exn_ when not (Common.Timer.is_async exn_) ->
                        Or_error.error_string
                          ("checker failed: " ^ Exn.to_string exn_)
                    with
                    | Ok _ -> None
                    | Error err ->
                        (* the run still goes on to the next problem *)
                        if print_sol then print_endline "unknown";
                        Some (sprintf "%s: %s" desc (Error.to_string_hum err))
                  in
                  Debug.print @@ lazy (sprintf "end checking %s" desc);
                  res)
            in
            if List.is_empty failures then Ok ()
            else
              Or_error.error_string
                ("the model checker gave no verdict for "
                ^ String.concat ~sep:"; " failures))
    | _ -> Or_error.unimplemented "solve_from_file"

  let solve_homc ?(print_sol = true) homc =
    let open Or_error.Monad_infix in
    match homc with
    | HOMC.Problem.EHMTT (ehmtt, trs, (main, typ)) ->
        solver >>= fun (module HOMCSolver : HOMCSolver.Solver.SolverType) ->
        HOMC.Reducer.solve_ehmtt ~print:Debug.print ~options:config.ehmtt
          ~solve:HOMCSolver.solve_rsfd ehmtt trs (main, typ)
        >>| fun sol ->
        if print_sol then print_endline (HOMC.Problem.str_of_solution sol);
        sol
    | HOMC.Problem.RSFD _ ->
        solver >>= fun (module HOMCSolver : HOMCSolver.Solver.SolverType) ->
        HOMCSolver.solve ~print_sol homc
end
