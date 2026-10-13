(* Configuration of the CHC optimization front door: which optimizing solver
   answers a CHC optimization problem.  OptPCSat is the only backend; the
   variant exists so that the dispatch has one place to grow. *)
open Core
open Common.Util

type t = OptPCSat of OptPCSat.Config.t [@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files =
  let open Or_error in
  function
  | OptPCSat cfg ->
      OptPCSat.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (OptPCSat cfg)

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "CHCOptSolver"
  let instantiate = instantiate_ext_files
end)
