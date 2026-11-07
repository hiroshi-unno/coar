(* Configuration of MuValQHFL: the RCaml configuration that types the OCaml
   representation of a quantitative lambda-HFL term in an expectation mode. *)

open Core
open Common.Util

type t = {
  verbose : bool; [@default false]
  rcaml : RCaml.Config.t;
      [@default Common.Util.config_default RCaml.Config.of_yojson {|{"verbose": false}|}]
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  let open Or_error in
  RCaml.Config.instantiate_ext_files cfg.rcaml >>= fun rcaml ->
  Ok { cfg with rcaml }

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "MuValQHFL"
  let instantiate = instantiate_ext_files
end)
