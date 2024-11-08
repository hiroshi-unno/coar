open Core

module type SolverType = sig
  val solve :
    ?print_sol:bool -> SAT.Problem.t -> SAT.Problem.solution Or_error.t

  val opt_solve :
    ?print_sol:bool ->
    SAT.Problem.soft ->
    SAT.Problem.t ->
    SAT.Problem.solution Or_error.t

  val incremental_solve : ?print_sol:bool -> SAT.Problem.t -> SAT.Problem.incsol
end

module Make (Cfg : Config.ConfigType) : SolverType = struct
  let config = Cfg.config

  let solve =
    match config with
    | Config.Z3Sat cfg ->
        let module Cfg = struct
          let config = cfg
        end in
        let module Z3Solver = Z3Sat.Solver.Make (Cfg) in
        Z3Solver.solve
    | Config.MiniSat cfg ->
        let module Cfg = struct
          let config = cfg
        end in
        let module MiniSat = MiniSat.Solver.Make (Cfg) in
        MiniSat.solve

  let opt_solve =
    match config with
    | Config.Z3Sat cfg ->
        let module Cfg = struct
          let config = cfg
        end in
        let module Z3Solver = Z3Sat.Solver.Make (Cfg) in
        Z3Solver.opt_solve
    | Config.MiniSat _ ->
        fun ?(print_sol = false) ->
          let _ = print_sol in
          failwith "not implemented"

  let incremental_solve =
    match config with
    | Config.Z3Sat cfg ->
        let module Cfg = struct
          let config = cfg
        end in
        let module Z3Solver = Z3Sat.Solver.Make (Cfg) in
        fun ?(print_sol = false) ->
          let _ = print_sol in
          failwith "not implemented"
    | Config.MiniSat cfg ->
        let module Cfg = struct
          let config = cfg
        end in
        let module MiniSat = MiniSat.Solver.Make (Cfg) in
        MiniSat.incremental_solve
end
