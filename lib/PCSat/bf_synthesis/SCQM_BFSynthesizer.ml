(* Placeholder learner of the Boolean-function synthesis dispatcher: it is
   accepted by the configuration and always returns an [unimplemented] error,
   so a configuration selecting it fails at its first synthesis call. *)
open Core

module Config = struct
  type t = { verbose : bool [@default false] } [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end
end

module Make (Cfg : Config.ConfigType) = struct
  let synthesize _ _ = Or_error.unimplemented "SCQM_BFSynthesizer.synthesize"
end
