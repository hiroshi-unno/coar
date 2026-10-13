open Core
open Common.Util

(* Predicate-abstraction synthesis: **the configuration exists, the synthesiser
   does not.**  [run_phase] below is [Or_error.unimplemented], the three fields
   [pa_format], [multi_sol] and [bcsp_solver] are read nowhere in [lib/], and no
   config in the corpus selects [Synthesizer.Config.PredicateAbstraction], which
   is the only way to reach this module.  A `-c` that did select it would fail at
   the first synthesis phase.  An option existing is no evidence that its path
   works, and this is that in its purest form: the JSON surface is complete and
   there is nothing behind it.  Kept because unreferenced paths are kept on
   purpose; documented so that it is not mistaken for a working backend. *)

type pa_format = CNF | Raw [@@deriving yojson]

module Config = struct
  type t = {
    qualifier : Qualifier.Generator.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/qualifier/tb.json"]
    sat_bCSP : SATSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/minisat.json"]
    pa_format : pa_format; [@default CNF]
    multi_sol : int; [@default 1]
    bcsp_solver : bool; [@default false] (* Bcspsolver.t *)
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
