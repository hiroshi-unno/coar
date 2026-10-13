(* Configuration of the HorSat2 wrapper: each Boolean field switches on the
   command-line flag of the same name ([-noce]: no counterexample is printed,
   [-merge], [-gfp]) of the external [horsat2] executable. *)
open Core
open Common.Util

type t = { verbose : bool; [@default false] noce : bool; [@default true] merge : bool; [@default false] gfp : bool [@default false] }
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg = Ok cfg

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "HorSat2"
  let instantiate = instantiate_ext_files
end)
