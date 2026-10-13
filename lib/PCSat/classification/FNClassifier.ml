(* Dispatcher for the classifiers of functional predicates: a template-based
   classifier or a regression-based one, chosen by the configuration.  Both
   return candidate definitions [(params, pvar, (args, phi))] for one
   predicate from its labelled truth table. *)
open Core
open Common.Util
open Ast
open Ast.LogicOld

module Config = struct
  type t = TB of TB_Classifier.Config.t | RGB of RGB_FNClassifier.Config.t
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let instantiate_ext_files = function
    | TB cfg ->
        let open Or_error in
        TB_Classifier.Config.instantiate_ext_files cfg >>= fun cfg ->
        Ok (TB cfg)
    | RGB cfg ->
        let open Or_error in
        RGB_FNClassifier.Config.instantiate_ext_files cfg >>= fun cfg ->
        Ok (RGB cfg)

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "FNClassifier"
    let instantiate = instantiate_ext_files
  end)
end

module type FNClassifierType = sig
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
                     (Problem) : FNClassifierType)
       | RGB cfg ->
           (module RGB_FNClassifier.Make
                     (struct
                       let config = cfg
                     end)
                     (Problem) : FNClassifierType))
