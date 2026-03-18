open Core
open Common.Util
open Preprocessing

type t = {
  preprocessor : Preprocessor.Config.t ext_file;
  timeout : int option;
  use_z3_native_mbp : bool;
  enable_global_guidance : bool;
  enable_z3_validation : bool;
  check_validity : bool;
  conservative_check : bool;
  solve_again_if_invalid : bool;
  solution_needed : bool;
  cex_needed : bool;
  verbose : bool;
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
          @@ sprintf "Invalid SPACER Configuration (%s): %s" filename msg)
