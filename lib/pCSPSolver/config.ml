open Core
open Common.Util

type t =
  | PCSat of PCSat.Config.t
  | SPACER of SPACER.Config.t
  | Hoice of Hoice.Config.t
  | Forward [@@ deriving yojson]

module type ConfigType = sig val config : t end 

let instantiate_ext_files = let open Or_error in
  function
  | PCSat cfg ->
    PCSat.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (PCSat cfg)
  | SPACER cfg ->
    SPACER.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (SPACER cfg)
  | Hoice cfg ->
    Hoice.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Hoice cfg)
  | Forward ->
    Ok Forward

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
          "Invalid PCSPSolver Configuration (%s): %s" filename msg
    end
  | Instance x -> Ok (ExtFile.Instance x)