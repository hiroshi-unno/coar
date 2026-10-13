(* Configuration of the HoIce wrapper: the timeout in seconds handed to the
   external [hoice] process, whether a proof is requested from it, and
   verbosity. *)
open Core
open Common.Util

type t = { timeout : int option; [@default None] produce_proofs : bool; [@default false] verbose : bool [@default false] }
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg = Ok cfg

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "Hoice"
  let instantiate = instantiate_ext_files
end)
