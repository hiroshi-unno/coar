open Core
open Z3
open Common

module type SolverType = sig
  type result = (SAT.Problem.solution, Error.t) Result.t

  val solve: ?print_sol:bool -> SAT.Problem.t -> result
end

module Make (Config: Config.ConfigType): SolverType = struct
  let config = Config.config

  module Debug = Debug.Make (val Debug.Config.(if config.verbose then enable else disable))

  type result = (SAT.Problem.solution, Error.t) Result.t

  let rec pos_exprs_of_strings ctx strings =
    match strings with
    | s::tl -> (Boolean.mk_const_s ctx s)::pos_exprs_of_strings ctx tl
    | [] -> []

  let rec neg_exprs_of_strings ctx strings =
    match strings with
    | s::tl -> (Boolean.mk_const_s ctx s |> Boolean.mk_not ctx):: neg_exprs_of_strings ctx tl
    | [] -> []

  let expr_of_clause ctx clause =
    match clause with
    | (negatives, positives) ->
      pos_exprs_of_strings ctx positives
      @ neg_exprs_of_strings ctx negatives
      |> Boolean.mk_or ctx

  let rec expr_of_cnf ctx cnf his=
    match cnf with
    | c::tl -> expr_of_cnf ctx tl ((expr_of_clause ctx c)::his)
    | [] -> his

  let solution_of_model model =   
    match model with
    | Some(model) ->
      let decls = Model.get_decls model in
      let assign = (List.map ~f:(
          fun decl ->
            match Model.get_const_interp model decl with
            | Some(expr) -> (FuncDecl.get_name decl|>Symbol.get_string, Boolean.is_true expr)
            | _ -> ("error", true)
        ) decls)
      in SAT.Problem.Sat assign
    | _ -> SAT.Problem.Unsat

  let solve ?(print_sol=false) cnf = 
    let clauses = SAT.Problem.to_list cnf in
    let cfg = ["model","true"; "proof", "true"] in
    let ctx = mk_context cfg in
    let exprs = expr_of_cnf ctx clauses [] in
    let solver = Solver.mk_solver ctx None in
    let _ = Solver.add solver exprs in
    let solution =
      match Solver.check solver [] with
      | Solver.SATISFIABLE ->
        Solver.get_model solver
        |> solution_of_model
        |> (fun solution ->
            let reduced_solution = if config.dim_reduction then SAT.Problem.Sat (SAT.Problem.minimize_core_cnf cnf (SAT.Problem.assign_of solution)) else solution in
            if config.dim_reduction then Debug.print @@ lazy (Printf.sprintf "z3: #vars reduced %d -> %d" (List.length (SAT.Problem.assign_of solution)) (List.length (SAT.Problem.assign_of reduced_solution)));
            reduced_solution)
      | _ -> SAT.Problem.Unsat
    in
    if print_sol then print_endline (SAT.Problem.str_of_solution solution);
    Ok solution
end
