(* Configuration of the Z3 SAT backend; [dim_reduction] as in the MiniSat
   backend: a model is shrunk greedily to a partial assignment that still
   satisfies every clause. *)
open Core
open Common.Util

type t = { dim_reduction : bool; [@default false] verbose : bool [@default false] } [@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg = Ok cfg

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "Z3Sat"
  let instantiate = instantiate_ext_files
end)
