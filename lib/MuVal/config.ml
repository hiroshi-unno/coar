open Core
open Common.Util

type mode =
  | Auto
  | Prove
  | Disprove
  | Parallel
  | ParallelExc  (** with exchange of learned clauses *)
[@@deriving yojson]

type t = {
  optimizer : MuCLP.Optimizer.Config.t ext_file;
  number_of_pairs : int;
  pcsp_solver_primal : PCSPSolver.Config.t ext_file;
  pcsp_solver_dual : PCSPSolver.Config.t ext_file;
  qelim : MuCLP.Qelim.Config.t;
  mode : mode;
  check_problem : bool;
  output_iteration : bool;
  output_yes_no : bool;
  verbose : bool;
  gen_extra_partial_sols : bool;
  random_ex_size : int;
  random_ex_bound : int;
  send_lower_bounds : bool;
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  Or_error.(
    PCSPSolver.Config.load_ext_file cfg.pcsp_solver_primal
    >>= fun pcsp_solver_primal ->
    PCSPSolver.Config.load_ext_file cfg.pcsp_solver_dual
    >>= fun pcsp_solver_dual ->
    MuCLP.Optimizer.Config.load_ext_file cfg.optimizer >>= fun optimizer ->
    MuCLP.Qelim.Config.instantiate_ext_files cfg.qelim >>= fun qelim ->
    Ok { cfg with pcsp_solver_primal; pcsp_solver_dual; optimizer; qelim })

let load_ext_file = function
  | ExtFile.Instance x -> Ok (ExtFile.Instance x)
  | Filename filename -> (
      let open Or_error in
      try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
      match of_yojson raw_json with
      | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
      | Error msg ->
          error_string
          @@ sprintf "Invalid MuVal Configuration (%s): %s" filename msg)
