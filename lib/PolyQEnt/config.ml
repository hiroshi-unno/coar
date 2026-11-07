(* Configuration of the PolyQEnt wrapper: the path of the external PolyQEnt
   executable and of its own configuration file ([None] for none), a
   timeout in milliseconds enforced by running it under [timeout], and a
   directory into which each query is copied before PolyQEnt runs on it
   ([None] for none), so that a query can be re-run by hand. *)
open Core
open Common.Util

type t = {
  path : string; [@default "./polyqent/PolyQEnt"]
  config_path : string option; [@default None]
  timeout_ms : int option; [@default None]
  query_copy_dir : string option; [@default None]
  verbose : bool; [@default false]
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg = Ok cfg

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "PolyQEnt"
  let instantiate = instantiate_ext_files
end)
