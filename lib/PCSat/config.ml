open Core
open Common.Util
open Coordination

type t = {
  (* main configuration *)
  coordinator: Coordinator.Config.t ext_file;
  pvar_eliminator: PvarEliminator.Config.t ext_file;
  solve_each_query: bool;
  check_problem: bool; (** check if the given pfw-CSP problem is well-formed. *)
  check_solution: bool;
  output_iteration: bool; (* TODO: generalize to output_format *)
  sygus_comp: bool;
} [@@ deriving yojson]

module type ConfigType = sig val config: t end

let instantiate_ext_files cfg =
  let open Or_error in
  Coordinator.Config.load_ext_file cfg.coordinator >>= fun coordinator ->
  PvarEliminator.Config.load_ext_file cfg.pvar_eliminator >>= fun pvar_eliminator ->
  Ok { cfg with coordinator = coordinator; pvar_eliminator = pvar_eliminator }

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
        error_string
        @@ Printf.sprintf
          "Invalid PCSat Configuration (%s): %s" filename msg
    end
  | Instance x -> Ok (Instance x)
