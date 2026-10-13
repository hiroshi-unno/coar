(* Configuration of the SMT solving layer: which backend answers a plain SMT
   problem (only Z3 today). *)
open Core
open Common.Util

type t = Z3Smt of Z3Smt.Config.t [@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files =
  let open Or_error in
  function
  | Z3Smt cfg ->
      Z3Smt.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Z3Smt cfg)

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "SMTSolver"
  let instantiate = instantiate_ext_files
end)
