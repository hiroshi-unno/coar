(* Configuration of the SAT solving layer: which backend answers a CNF
   problem, each carrying its own configuration. *)
open Core
open Common.Util

type t =
  | Z3Sat of Z3Sat.Config.t
  | MiniSat of MiniSat.Config.t
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files =
  let open Or_error in
  function
  | Z3Sat cfg ->
      Z3Sat.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Z3Sat cfg)
  | MiniSat cfg ->
      MiniSat.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (MiniSat cfg)

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "SATSolver"
  let instantiate = instantiate_ext_files
end)
