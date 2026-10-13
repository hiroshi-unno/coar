(* Configuration of the MiniSat backend.  [dim_reduction] shrinks a found model
   to a greedy subset of its assignments that still satisfies every clause, so
   a reported model may be partial (an absent variable is a don't-care). *)
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
  let name = "MiniSat"
  let instantiate = instantiate_ext_files
end)
