(* Configuration of HOMCSat, the solver for SAT, DQSAT and higher-order
   Boolean satisfiability problems that reduces them to higher-order model
   checking: the model checker to use, and whether implication, equivalence
   and exclusive or are rewritten into negation, conjunction and disjunction
   before translation instead of being kept as terminals of their own. *)
open Core
open Common.Util

type t = {
  verbose : bool; [@default false]
  solver : HOMCSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/horsat2.json"]
  encode_bool_ops : bool; [@default false]
}
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
  let name = "HOMCSat"
  let instantiate = instantiate_ext_files
end)
