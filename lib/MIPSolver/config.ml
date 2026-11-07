open Core
open Common.Util

(* [Best_available] is Gurobi where this build has it (the `lp-gurobi`
   package is installed) and GLPK otherwise; [Gurobi] asks for Gurobi and is
   an error in a build without it. *)
type mode = Glpk | Gurobi | Best_available [@@deriving yojson]

type t = {
  engine : mode; [@default Best_available]
  verbose : bool; [@default false]
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg = Ok cfg

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "MIPSolver"
  let instantiate = instantiate_ext_files
end)
