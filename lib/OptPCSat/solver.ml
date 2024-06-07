open Core

module type SolverType = sig
  type solution = string * PCSP.Problem.solution * int

  val solve :
    ?filename:string option ->
    ?print_sol:bool ->
    CHCOpt.Problem.t ->
    CHCOpt.Problem.solution * int
end

module Make (Config : Config.ConfigType) : SolverType = struct
  type solution = string * PCSP.Problem.solution * int

  let config = Config.config

  let solve ?(filename = None) ?(print_sol = false) problem =
    let (dir_map, priority, fronts), pcsp = problem in
    let not_opt_checker =
      LexicoNonOptChecker.make config.verbose dir_map fronts
        config.improve_current
    in
    let (module Optimizer : Optimizer.OptimizerType) =
      Optimizer.make Config.config not_opt_checker
    in
    let sol, iter = Optimizer.optimize ~filename priority pcsp in
    if print_sol then
      print_endline
      @@ CHCOpt.Problem.str_of_solution (PCSP.Problem.senv_of pcsp) iter sol;
    (sol, iter)
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolverType)
