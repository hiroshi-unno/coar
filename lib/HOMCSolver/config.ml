open Core
open Common.Util

type t = TRecS of TRecS.Config.t | HorSat2 of HorSat2.Config.t
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files =
  let open Or_error in
  function
  | TRecS cfg ->
      TRecS.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (TRecS cfg)
  | HorSat2 cfg ->
      HorSat2.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (HorSat2 cfg)

let load_ext_file = function
  | ExtFile.Instance x -> Ok (ExtFile.Instance x)
  | Filename filename -> (
      let open Or_error in
      try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
      match of_yojson raw_json with
      | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
      | Error msg ->
          error_string
          @@ sprintf "Invalid HOMCSolver Configuration (%s): %s" filename msg)
