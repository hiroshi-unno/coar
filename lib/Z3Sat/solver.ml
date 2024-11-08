open Core
open Common

module type SolverType = sig
  val solve :
    ?print_sol:bool -> SAT.Problem.t -> SAT.Problem.solution Or_error.t

  val opt_solve :
    ?print_sol:bool ->
    SAT.Problem.soft ->
    SAT.Problem.t ->
    SAT.Problem.solution Or_error.t
end

module Make (Config : Config.ConfigType) : SolverType = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let solve ?(print_sol = false) cnf =
    let solution =
      match Z3interface.solve cnf with
      | None -> SAT.Problem.Unsat
      | Some sol ->
          if config.dim_reduction then (
            let red_sol = SAT.Problem.minimize_core_cnf cnf sol in
            Debug.print
            @@ lazy
                 (sprintf "#vars reduced %d -> %d" (List.length sol)
                    (List.length red_sol));
            SAT.Problem.Sat red_sol)
          else SAT.Problem.Sat sol
    in
    if print_sol then print_endline (SAT.Problem.str_of_solution solution);
    Ok solution

  let opt_solve ?(print_sol = false) soft cnf =
    let solution =
      match Z3interface.opt_solve soft cnf with
      | None -> SAT.Problem.Unsat
      | Some (_score, sol) ->
          if config.dim_reduction then (
            let red_sol = SAT.Problem.minimize_core_cnf cnf sol in
            Debug.print
            @@ lazy
                 (sprintf "#vars reduced %d -> %d" (List.length sol)
                    (List.length red_sol));
            SAT.Problem.Sat red_sol)
          else SAT.Problem.Sat sol
    in
    if print_sol then print_endline (SAT.Problem.str_of_solution solution);
    Ok solution
end
