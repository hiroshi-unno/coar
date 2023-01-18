open Core
open Common.Util

type t =
  | Z3Sat of Z3Sat.Config.t
  | Minisat of MINISAT.Config.t
  [@@ deriving yojson]

module type ConfigType = sig val config : t end

let instantiate_ext_files = let open Or_error in
  function
  | Z3Sat cfg ->
    Z3Sat.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Z3Sat cfg)
  | Minisat cfg ->
    MINISAT.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Minisat cfg)

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
          "Invalid SATSolver Configuration (%s): %s" filename msg
    end
  | Instance x -> Ok (ExtFile.Instance x)
