open Core
open Common.Util

module type BFSynthesizerType = sig
  val synthesize: PCSatCommon.TruthTable.table-> Ast.PropLogic.Formula.t Or_error.t
end

module Config = struct
  type t =
    | DTBF of DT_BFSynthesizer.Config.t
    | SCQMBF of SCQM_BFSynthesizer.Config.t [@@deriving yojson]

  module type ConfigType = sig val config : t end

  let load_ext_file = function
    | ExtFile.Filename filename ->
      begin
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename)
        >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> Ok (ExtFile.Instance x)
        | Error msg ->
          error_string
          @@ Printf.sprintf
            "Invalid BFSynthesizer Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (ExtFile.Instance x)
end

module Make (Cfg: Config.ConfigType)
  : BFSynthesizerType =
  (val (match Cfg.config with
       | DTBF cfg -> (module (DT_BFSynthesizer.Make (struct let config = cfg end))
                       : BFSynthesizerType)
       | SCQMBF cfg -> (module (SCQM_BFSynthesizer.Make (struct let config = cfg end))
                         : BFSynthesizerType)))
