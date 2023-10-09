open Core
open Common.Util
open Coordination

type t = {
  (* main configuration *)
  coordinator: Coordinator.Config.t ext_file;
  pvar_eliminator: PvarEliminator.Config.t ext_file;
  sol_printer: SolPrinter.Config.t ext_file;
  load_oracle_sol: bool;
  solve_each_query: bool; (** solve each query independently *)
  check_problem: bool; (** check the well-formedness of the input pfwCSP *)
  check_solution: bool; (** check the correctness of the output solution *)
} [@@ deriving yojson]

module type ConfigType = sig val config: t end

let instantiate_ext_files cfg =
  let open Or_error in
  Coordinator.Config.load_ext_file cfg.coordinator >>= fun coordinator ->
  PvarEliminator.Config.load_ext_file cfg.pvar_eliminator >>= fun pvar_eliminator ->
  SolPrinter.Config.load_ext_file cfg.sol_printer >>= fun sol_printer ->
  Ok { cfg with coordinator = coordinator;
                pvar_eliminator = pvar_eliminator;
                sol_printer = sol_printer }

let load_ext_file = function
  | ExtFile.Instance x -> Ok (ExtFile.Instance x)
  | Filename filename ->
    let open Or_error in
    try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
    match of_yojson raw_json with
    | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
    | Error msg ->
      error_string @@ sprintf "Invalid PCSat Configuration (%s): %s" filename msg
