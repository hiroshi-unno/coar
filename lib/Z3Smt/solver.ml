open Core
open Common

module type SolverType = sig
  val solve :
    ?print_sol:bool -> SMT.Problem.t -> SMT.Problem.solution Or_error.t
end

module Make (Config : Config.ConfigType) : SolverType = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let solve ?(print_sol = false) phi =
    Debug.print @@ lazy ("input: " ^ Ast.LogicOld.Formula.str_of phi);
    let fenv = Map.Poly.empty (* TODO *) in
    match Z3interface.check_sat ~id:None fenv [ phi ] with
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
