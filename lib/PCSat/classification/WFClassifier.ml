(* Dispatcher for the classifiers of well-founded predicates: the
   template-based classifier or the decision-tree ranking-function learner,
   chosen by the configuration. *)
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

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "WFClassifier"
    let instantiate = instantiate_ext_files
  end)
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
