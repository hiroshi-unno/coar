open Core
open Common.Util
open Ast.LogicOld

module Config = struct
  type t = DT of DT_Regressor.Config.t [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let instantiate_ext_files = function
    | DT cfg ->
        let open Or_error in
        DT_Regressor.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (DT cfg)

  let load_ext_file = function
    | ExtFile.Instance x -> Ok (ExtFile.Instance x)
    | Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
        | Error msg ->
            error_string
            @@ sprintf "Invalid Regressor Configuration (%s): %s" filename msg)
end

module type RegressorType = sig
  val mk_regressor :
    sort_env_list ->
    (PCSatCommon.ExAtom.t * int) Set.Poly.t ->
    (sort_env_map * Term.t) Or_error.t
end

module Make (Cfg : Config.ConfigType) =
  (val match Cfg.config with
       | DT cfg ->
           (module DT_Regressor.Make (struct
             let config = cfg
           end) : RegressorType))
