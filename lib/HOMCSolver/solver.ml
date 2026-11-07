(* Dispatch for higher-order model checking problems: instantiates the TRecS
   or HorSat2 wrapper the configuration names and returns its [solve], and its
   [solve_rsfd] for one HORS problem.  Either wrapper reads a HORS problem of
   either automaton dialect, translating it into the one its checker reads,
   so a caller (EffCaml, HOMCSat) may hand either kind to either checker; an
   input the checker cannot read and no translation reaches is an [Error],
   not a verdict. *)
open Core

module type SolverType = sig
  val solve :
    ?print_sol:bool -> HOMC.Problem.t -> HOMC.Problem.solution Or_error.t

  (* Decide one HORS problem, of either automaton dialect, answering the
     verdict together with the checker's counterexample when it printed one
     and the wrapper kept the refutation.  A translation that fails (rules
     that are not simply sorted, an automaton outside the translation's
     fragment) is an [Error]. *)
  val solve_rsfd :
    HOMC.Problem.t -> (HOMC.Problem.solution * string option) Or_error.t
end

module Make (Cfg : Config.ConfigType) : SolverType = struct
  let config = Cfg.config

  let solve, solve_rsfd =
    match config with
    | Config.TRecS cfg ->
        let module TRecS = TRecS.Solver.Make (struct
          let config = cfg
        end) in
        ((fun ?print_sol homc -> TRecS.solve ?print_sol homc), TRecS.solve_rsfd)
    | Config.HorSat2 cfg ->
        let module HorSat2 = HorSat2.Solver.Make (struct
          let config = cfg
        end) in
        ( (fun ?print_sol homc -> HorSat2.solve ?print_sol homc),
          HorSat2.solve_rsfd )
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolverType)
