open Core
open Common.Util

type mode =
  | Auto | Prove | Disprove | Parallel
  | ParallelExc (** with exchange of learned clauses *)
[@@deriving yojson]

type t = {
  pcsp_solver : PCSPSolver.Config.t ext_file;
  optimizer : MuCLP.Optimizer.Config.t ext_file;
  qelim : MuCLP.Qelim.Config.t;
  mode : mode;
  check_problem : bool;
  output_iteration : bool;
  verbose : bool;
  gen_extra_partial_sols : bool;
  random_ex_size : int;
  random_ex_bound : int
} [@@deriving yojson]

module type ConfigType = sig val config: t end

let instantiate_ext_files cfg =
  Or_error.
    (PCSPSolver.Config.load_ext_file cfg.pcsp_solver >>= fun pcsp_solver ->
     MuCLP.Optimizer.Config.load_ext_file cfg.optimizer >>= fun optimizer ->
     MuCLP.Qelim.Config.instantiate_ext_files cfg.qelim >>= fun qelim ->
     Ok { cfg with pcsp_solver = pcsp_solver; optimizer = optimizer; qelim = qelim })

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
          "Invalid MuVal Configuration (%s): %s" filename msg
    end
  | Instance x -> Ok (Instance x)
