(* Configuration of the TRecS wrapper.  The external [trecs] executable takes no
   options from here; only this tree's tracing is configurable. *)
open Core
open Common.Util

type t = { verbose : bool [@default false] } [@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg = Ok cfg

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "TRecS"
  let instantiate = instantiate_ext_files
end)
