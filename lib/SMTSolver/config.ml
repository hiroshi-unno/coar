open Core
open Common.Util

type t = Z3Smt of Z3Smt.Config.t [@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files =
  let open Or_error in
  function
  | Z3Smt cfg ->
      Z3Smt.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Z3Smt cfg)

let load_ext_file = function
  | ExtFile.Instance x -> Ok (ExtFile.Instance x)
  | Filename filename -> (
      let open Or_error in
      try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
      match of_yojson raw_json with
      | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
      | Error msg ->
          error_string
          @@ sprintf "Invalid SMTSolver Configuration (%s): %s" filename msg)
