(* Dispatcher for the classifiers of ordinary predicates used by the
   classification-based synthesizer: a template-based classifier or a
   Boolean-function synthesis over qualifiers, chosen by the configuration.
   Every classifier answers [mk_classifier pvar params table labeling
   examples] with candidate definitions of [pvar] over [params]. *)
open Core
open Common.Util
open Ast
open Ast.LogicOld

module Config = struct
  type t = TB of TB_Classifier.Config.t | BFSB of BFSB_Classifier.Config.t
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let instantiate_ext_files = function
    | TB cfg ->
        let open Or_error in
        TB_Classifier.Config.instantiate_ext_files cfg >>= fun cfg ->
        Ok (TB cfg)
    | BFSB cfg ->
        let open Or_error in
        BFSB_Classifier.Config.instantiate_ext_files cfg >>= fun cfg ->
        Ok (BFSB cfg)

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "Classifier"
    let instantiate = instantiate_ext_files
  end)
end

module type ClassifierType = sig
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
                     (Problem) : ClassifierType)
       | BFSB cfg ->
           (module BFSB_Classifier.Make
                     (struct
                       let config = cfg
                     end)
                     (Problem) : ClassifierType))
