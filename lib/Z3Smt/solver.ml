open Core
open Common

module type SolverType = sig
  type result = (SMT.Problem.solution, Error.t) Result.t

  val solve: ?print_sol:bool -> SMT.Problem.t -> result
end

module Make (Config: Config.ConfigType): SolverType = struct
  let config = Config.config

  module Debug = Debug.Make (val (Debug.Config.(if config.verbose then enable else disable)))

  type result = (SMT.Problem.solution, Error.t) Result.t

  let solve ?(print_sol=false) phi =
    Debug.print @@ lazy ("input: " ^ Ast.LogicOld.Formula.str_of phi);
    match Z3interface.check_sat Set.Poly.empty [phi] with
    | `Sat model ->
      let solution = SMT.Problem.Sat model in
      if print_sol then print_endline (SMT.Problem.str_of_solution solution);
      Ok solution
    | `Unsat ->
      let solution = SMT.Problem.Unsat in
      if print_sol then print_endline (SMT.Problem.str_of_solution solution);
      Ok solution
    | `Timeout -> Or_error.error_string "timeout"
    | `Unknown reason -> Or_error.error_string reason
end

