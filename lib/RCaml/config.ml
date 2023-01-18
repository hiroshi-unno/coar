open Core
open Common.Util

type t = {
  solver : PCSPSolver.Config.t ext_file;
  optimizer : CHCOptSolver.Config.t ext_file;
  cgen_config : Ast.Rtype.config;
  verbose : bool;
  printer : bool;
  timeout : int option
} [@@ deriving yojson]

module type ConfigType = sig val config : t end

let instantiate_ext_files cfg = let open Or_error in
  PCSPSolver.Config.load_ext_file cfg.solver >>= fun solver ->
  CHCOptSolver.Config.load_ext_file cfg.optimizer >>= fun optimizer ->
  Ok { cfg with solver; optimizer = optimizer }

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
          "Invalid RCaml Configuration (%s): %s" filename msg
    end
  | Instance x -> Ok (Instance x)
