(* Dispatch for CHC optimization problems (a CHC system with a direction per
   predicate and a priority order between them): builds the configured
   optimizer, today always OptPCSat, and forwards [solve] to it unchanged. *)
module type SolverType = sig
  val solve :
    ?print_sol:bool -> CHCOpt.Problem.t -> CHCOpt.Problem.solution * int
end

module Make (Cfg : Config.ConfigType) : SolverType = struct
  let config = Cfg.config

  type solver = SOptPCSat of (module OptPCSat.Solver.SolverType)

  let solver =
    match config with
    | Config.OptPCSat cfg -> SOptPCSat (OptPCSat.Solver.make cfg)

  let solve =
    match solver with
    | SOptPCSat (module OptPCSat) ->
        fun ?(print_sol = false) pcsp -> OptPCSat.solve ~print_sol pcsp
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolverType)
