open Core

module type SolverType = sig
  type result = (SAT.Problem.solution, Error.t) Result.t

  val solve: ?print_sol:bool -> SAT.Problem.t -> result
  val incremental_solve:  ?print_sol:bool -> SAT.Problem.t -> SAT.Problem.incsol
end

module Make (Cfg: Config.ConfigType):SolverType = struct
  let config = Cfg.config

  type result = (SAT.Problem.solution, Error.t) Result.t

  let solve =
    match config with
    | Config.Z3Sat cfg ->
      let module Cfg = struct let config = cfg end in
      let module Z3Solver = Z3Sat.Solver.Make(Cfg) in
      Z3Solver.solve
    | Config.Minisat cfg ->
      let module Cfg = struct let config = cfg end in
      let module Minisat = MINISAT.Solver.Make(Cfg) in
      Minisat.solve

  let incremental_solve =     
    match config with
    | Config.Z3Sat cfg ->
      let module Cfg = struct let config = cfg end in
      let module Z3Solver = Z3Sat.Solver.Make(Cfg) in
      fun ?(print_sol=false) _ -> let _ = print_sol in assert false
    | Config.Minisat cfg ->
      let module Cfg = struct let config = cfg end in
      let module Minisat = MINISAT.Solver.Make(Cfg) in
      Minisat.incremental_solve
end
