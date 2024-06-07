open Core
open Common.Util
open Preprocessing

type lts_format = MuCLP | PCSP [@@deriving yojson]
type smt_format = String | SMT2 [@@deriving yojson]

type t = {
  preprocessor : Preprocessor.Config.t ext_file;
  lts_format : lts_format;
  smt_format : smt_format;
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  let open Or_error in
  Preprocessor.Config.load_ext_file cfg.preprocessor >>= fun preprocessor ->
  Ok { cfg with preprocessor }

let load_ext_file = function
  | ExtFile.Instance x -> Ok (ExtFile.Instance x)
  | Filename filename -> (
      let open Or_error in
      try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
      match of_yojson raw_json with
      | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
      | Error msg ->
          error_string
          @@ sprintf "Invalid Printer Configuration (%s): %s" filename msg)
