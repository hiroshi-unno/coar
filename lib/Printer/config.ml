open Core
open Common.Util

type lts_format = MuCLP | PCSP [@@ deriving yojson]
type smt_format = String | SMT2  [@@ deriving yojson]
type t = {
  pvar_eliminator: PCSat.PvarEliminator.Config.t ext_file;
  lts_format : lts_format;
  smt_format : smt_format
} [@@ deriving yojson]

module type ConfigType = sig val config : t end

let instantiate_ext_files cfg =
  let open Or_error in
  PCSat.PvarEliminator.Config.load_ext_file cfg.pvar_eliminator >>= fun pvar_eliminator ->
  Ok { cfg with pvar_eliminator = pvar_eliminator }

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
          "Invalid Printer Configuration (%s): %s" filename msg
    end
  | Instance x -> Ok (Instance x)