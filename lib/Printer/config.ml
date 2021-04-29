open Core
open Common.Util

type mode = MuCLP | PCSP [@@ deriving yojson]
type t = {
  mode: mode;
} [@@ deriving yojson]

module type ConfigType = sig val config : t end

let instantiate_ext_files cfg = Ok cfg

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
          "Invalid Printer Configuration (%s): %s" filename msg
    end
  | Instance x -> Ok (Instance x)