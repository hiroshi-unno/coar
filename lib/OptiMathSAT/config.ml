(* Configuration of the OptiMathSAT wrapper: the executable's path, an
   optional timeout and tracing. *)
open Core
open Common.Util

type t = { path : string; [@default "./optimathsat.exe"] timeout : int option; [@default None] verbose : bool [@default false] }
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg = Ok cfg

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "OptiMathSAT"
  let instantiate = instantiate_ext_files
end)
