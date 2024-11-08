open Core

module type SolverType = sig
  val solve :
    ?print_sol:bool -> HOMC.Problem.t -> HOMC.Problem.solution Or_error.t
end

module Make (Cfg : Config.ConfigType) : SolverType = struct
  let config = Cfg.config

  let solve =
    match config with
    | Config.TRecS cfg ->
        let module Cfg = struct
          let config = cfg
        end in
        let module TRecS = TRecS.Solver.Make (Cfg) in
        TRecS.solve
    | Config.HorSat2 cfg ->
        let module Cfg = struct
          let config = cfg
        end in
        let module HorSat2 = HorSat2.Solver.Make (Cfg) in
        HorSat2.solve
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolverType)
