open Core
open Common.Util

type pa_format = CNF | Raw [@@deriving yojson]

module Config = struct
  type t = {
    qualifier : Qualifier.Generator.Config.t ext_file;
    sat_bCSP : SATSolver.Config.t ext_file;
    pa_format : pa_format;
    multi_sol : int;
    bcsp_solver : bool; (* Bcspsolver.t *)
  }
  [@@deriving yojson]

  let instantiate_ext_files cfg =
    let open Or_error in
    Qualifier.Generator.Config.load_ext_file cfg.qualifier >>= fun qualifier ->
    SATSolver.Config.load_ext_file cfg.sat_bCSP >>= fun sat_bCSP ->
    Ok { cfg with qualifier; sat_bCSP }

  module type ConfigType = sig
    val config : t
  end
end

module Make (Cfg : Config.ConfigType) (Problem : PCSP.Problem.ProblemType) =
struct
  let run_phase _ _ = Or_error.unimplemented "PASynthesizer.run_phase"
  let init () = () (*ToDo*)
end
