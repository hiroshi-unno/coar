(* Configuration of the higher-order model checking front door: which external
   model checker decides a HORS or EHMTT problem, TRecS (trivial tree automata)
   or HorSat2 (alternating tree automata). *)
open Core
open Common.Util

type t = TRecS of TRecS.Config.t | HorSat2 of HorSat2.Config.t
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files =
  let open Or_error in
  function
  | TRecS cfg ->
      TRecS.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (TRecS cfg)
  | HorSat2 cfg ->
      HorSat2.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (HorSat2 cfg)

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "HOMCSolver"
  let instantiate = instantiate_ext_files
end)
