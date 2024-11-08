open Core
open Common.Util

type t = { verbose : bool; solver : HOMCSolver.Config.t ext_file }
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  let open Or_error in
  HOMCSolver.Config.load_ext_file cfg.solver >>= fun solver ->
  Ok { cfg with solver }

let load_ext_file = function
  | ExtFile.Instance x -> Ok (ExtFile.Instance x)
  | Filename filename -> (
      let open Or_error in
      try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
      match of_yojson raw_json with
      | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
      | Error msg ->
          error_string
          @@ sprintf "Invalid EffCaml Configuration (%s): %s" filename msg)
