(* Dispatcher for the regressors that fit a result term to a functional
   predicate's labelled examples: [mk_regressor args labeled] returns the
   term over [args] and the template parameters left in it.  One learner is
   configurable today. *)
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

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "Regressor"
    let instantiate = instantiate_ext_files
  end)
end

module type RegressorType = sig
  val mk_regressor :
    sort_env_list ->
    (Ast.ExAtom.t * int) Set.Poly.t ->
    (sort_env_map * Term.t) Or_error.t
end

module Make (Cfg : Config.ConfigType) =
  (val match Cfg.config with
       | DT cfg ->
           (module DT_Regressor.Make (struct
             let config = cfg
           end) : RegressorType))
