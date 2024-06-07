open Core

module Config = struct
  type t = { verbose : bool } [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end
end

module Make (Cfg : Config.ConfigType) = struct
  let synthesize _ _ = Or_error.unimplemented "SCQM_BFSynthesizer.synthesize"
end
