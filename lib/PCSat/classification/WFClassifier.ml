open Core
open Common.Util
open Ast
open Ast.LogicOld

module Config = struct
  type t = TB of TB_Classifier.Config.t | DT of DT_WFClassifier.Config.t
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let instantiate_ext_files = function
    | TB cfg ->
        let open Or_error in
        TB_Classifier.Config.instantiate_ext_files cfg >>= fun cfg ->
        Ok (TB cfg)
    | DT cfg ->
        let open Or_error in
        DT_WFClassifier.Config.instantiate_ext_files cfg >>= fun cfg ->
        Ok (DT cfg)

  let load_ext_file = function
    | ExtFile.Instance x -> Ok (ExtFile.Instance x)
    | Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
        | Error msg ->
            error_string
            @@ sprintf "Invalid WFClassifier Configuration (%s): %s" filename
                 msg)
end

module type WFClassifierType = sig
  type classifier = sort_env_map * (Ident.pvar * (sort_env_list * Formula.t))

  val mk_classifier :
    Ident.pvar ->
    sort_env_list ->
    PCSatCommon.TruthTable.t ->
    (int, int) Map.Poly.t ->
    sort_env_map * PCSatCommon.VersionSpace.examples ->
    classifier list Or_error.t
end

module Make (Cfg : Config.ConfigType) (Problem : PCSP.Problem.ProblemType) =
  (val match Cfg.config with
       | TB cfg ->
           (module TB_Classifier.Make
                     (struct
                       let config = cfg
                     end)
                     (Problem) : WFClassifierType)
       | DT cfg ->
           (module DT_WFClassifier.Make
                     (struct
                       let config = cfg
                     end)
                     (Problem) : WFClassifierType))
