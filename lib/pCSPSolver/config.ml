(* Configuration of the pfwCSP solver front door used by mid-level solvers: one
   of PCSat, Spacer, HoIce, PolyQEnt, forward propagation, or the Printer (which
   only prints the problem and answers unknown). *)
open Core
open Common.Util

type t =
  | PCSat of PCSat.Config.t
  | SPACER of SPACER.Config.t
  | Hoice of Hoice.Config.t
  | PolyQEnt of PolyQEnt.Config.t
  | Forward
  | Printer of Printer.Config.t
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files =
  let open Or_error in
  function
  | PCSat cfg ->
      PCSat.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (PCSat cfg)
  | SPACER cfg ->
      SPACER.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (SPACER cfg)
  | Hoice cfg ->
      Hoice.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Hoice cfg)
  | PolyQEnt cfg ->
      PolyQEnt.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (PolyQEnt cfg)
  | Forward -> Ok Forward
  | Printer cfg ->
      Printer.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Printer cfg)

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "PCSPSolver"
  let instantiate = instantiate_ext_files
end)
