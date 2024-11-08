open Core
(* open Common.Util *)

module type SmtSolverType = sig
  val solve : SMT.Problem.t -> SMT.Problem.solution Or_error.t
end

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  let solve =
    match config with
    | Config.Z3Smt cfg ->
        let module Cfg = struct
          let config = cfg
        end in
        let module Z3SmtSolver = Z3Smt.Solver.Make (Cfg) in
        Z3SmtSolver.solve
end
