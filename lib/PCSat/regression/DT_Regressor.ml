open Core
open Common
open Ast.LogicOld

module Config = struct
  type t = { verbose : bool } [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let instantiate_ext_files cfg = Ok cfg
end

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let mk_regressor _params _labeled_atoms =
    Ok ((*ToDo*) Map.Poly.empty, Term.mk_dummy T_int.SInt)
end
