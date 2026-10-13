(* Configuration of RCaml: the predicate constraint solver for assertion
   problems ([solver]), the CHC optimizer for type-optimization problems
   ([optimizer]), the refinement-type constraint generator's own settings
   ([cgen_config]), whether predicate variables are eliminated before solving
   ([enable_pvar_elim]), and a per-problem timeout in seconds. *)

open Core
open Common.Util

type t = {
  solver : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/pcsat_tb_ar.json"]
  optimizer : CHCOptSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/optpcsat_nc_tb_ar.json"]
  cgen_config : Ast.Rtype.config; [@default Common.Util.config_default Ast.Rtype.config_of_yojson "{}"]
  verbose : bool; [@default true]
  enable_pvar_elim : bool; [@default true]
  timeout : int option; [@default None]
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  let open Or_error in
  PCSPSolver.Config.load_ext_file cfg.solver >>= fun solver ->
  CHCOptSolver.Config.load_ext_file cfg.optimizer >>= fun optimizer ->
  Ok { cfg with solver; optimizer }

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "RCaml"
  let instantiate = instantiate_ext_files
end)
