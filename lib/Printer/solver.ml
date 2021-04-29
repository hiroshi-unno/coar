open Core

module type SolverType = sig
  val print_pcsp: PCSP.Problem.t -> unit
  val print_muclp: MuCLP.Problem.t -> unit
  val print_lts: LTS.Problem.t -> unit
end

module Make (Config: Config.ConfigType): SolverType = struct
  let config = Config.config

  let print_pcsp pcsp = print_endline (PCSP.Problem.str_of pcsp)
  let print_muclp muclp = print_endline (MuCLP.Problem.str_of muclp)
  let print_lts lts =
    match config.mode with
    | PCSP -> print_endline (PCSP.Problem.str_of (PCSP.Problem.of_lts lts))
    | MuCLP -> print_endline (MuCLP.Problem.str_of (MuCLP.Problem.of_lts lts))
end