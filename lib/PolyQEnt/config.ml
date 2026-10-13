(* Configuration of the PolyQEnt wrapper: the path of the external PolyQEnt
   executable and of its own configuration file (empty for none), and a
   timeout in milliseconds enforced by running it under [timeout]. *)
open Core
open Common.Util

type t = {
  path : string; [@default "./polyqent/PolyQEnt"]
  config_path : string; [@default ""]
  timeout : int option; [@default None]
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
