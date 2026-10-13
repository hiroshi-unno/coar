(* Configuration of EffCaml: whether to trace, and the higher-order model
   checker ([HOMCSolver]) its generated problems are handed to. *)

open Core
open Common.Util

type t = { verbose : bool; [@default false] solver : HOMCSolver.Config.t ext_file [@default Common.Util.ExtFile.Filename "./config/solver/horsat2_ce.json"] }
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  let open Or_error in
  HOMCSolver.Config.load_ext_file cfg.solver >>= fun solver ->
  Ok { cfg with solver }

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "EffCaml"
  let instantiate = instantiate_ext_files
end)
