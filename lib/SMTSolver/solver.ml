open Core
(* open Common.Util *)


module type SmtSolverType = sig
  type result = (SMT.Problem.solution, Error.t) Result.t

  val solve : SMT.Problem.t -> result
end

module Make (Cfg: Config.ConfigType) = struct
  let config = Cfg.config

  type result = (SMT.Problem.solution, Error.t) Result.t

  let solve =
    match config with
    | Config.Z3Smt cfg ->
      let module Cfg = struct let config = cfg end in
      let module Z3SmtSolver = Z3Smt.Solver.Make(Cfg) in
      Z3SmtSolver.solve
end
