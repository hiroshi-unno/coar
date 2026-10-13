(* Configuration of OptPCSat: the constraint solvers used to improve a
   solution and to check its optimality, whether to start from a seed
   solution read beside the input, whether improvement considers the whole
   priority list or only the predicates not yet optimized, the side-condition
   mode (none, non-trivial or non-vacuous solutions), and how an optimality
   certificate that is not known to be exact is treated. *)
open Core
open Common.Util

type mode = NoSideCond | NonTrivial | NonVacuous [@@deriving yojson]

type t = {
  load_init_sol : bool; [@default false]
  improve_solver : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/pcsat_tb_interval3.json"]
  opt_check_solver : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/pcsat_tb.json"]
  verbose : bool; [@default false]
  one_by_one : bool; [@default true]
  improve_current : bool; [@default false]
  mode : mode; [@default NoSideCond]
  (* accept the optimality checker's certificate only when it is exact;
     [false] treats every certificate as exact and accepts it at once *)
  exact_opt_check : bool; [@default true]
  (* seconds the improver gets to refute an inexact certificate before it is
     accepted anyway *)
  inexact_certificate_wait : float; [@default 5.0]
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let is_non_trival_mode = function NonTrivial -> true | _ -> false
let is_non_vacuous_mode = function NonVacuous -> true | _ -> false

let instantiate_ext_files cfg =
  let open Or_error in
  PCSPSolver.Config.load_ext_file cfg.improve_solver >>= fun improve_solver ->
  PCSPSolver.Config.load_ext_file cfg.opt_check_solver
  >>= fun opt_check_solver -> Ok { cfg with improve_solver; opt_check_solver }

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "OptPCSat"
  let instantiate = instantiate_ext_files
end)
