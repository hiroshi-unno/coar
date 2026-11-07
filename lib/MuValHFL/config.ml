(* Configuration of MuValHFL: the RCaml configuration that types the OCaml
   representation in the Boolean HFL mode ([rcaml]); an optional MuVal
   configuration that order-1 inputs go to instead ([order1_backend], none by
   default: every input goes to RCaml); the dialect HES files are read in
   ([dialect]: ["coar"], the union, by default, or ["rethfl"], ["hflmc2"],
   ["muhfl"]); and the refutation of a formula RCaml cannot type by bounded
   unfolding ([refute_by_unfolding], off until measured, up to
   [unfolding_depth] unfoldings). *)

open Core
open Common.Util

type t = {
  verbose : bool; [@default false]
  rcaml : RCaml.Config.t;
      [@default Common.Util.config_default RCaml.Config.of_yojson {|{"verbose": false}|}]
  order1_backend : MuVal.Config.t ext_file option; [@default None]
  dialect : string; [@default "coar"]
  refute_by_unfolding : bool; [@default false]
  unfolding_depth : int; [@default 4]
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  let open Or_error in
  RCaml.Config.instantiate_ext_files cfg.rcaml >>= fun rcaml ->
  (match cfg.order1_backend with
  | None -> Ok None
  | Some f -> MuVal.Config.load_ext_file f >>| Option.some)
  >>= fun order1_backend -> Ok { cfg with rcaml; order1_backend }

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "MuValHFL"
  let instantiate = instantiate_ext_files
end)
