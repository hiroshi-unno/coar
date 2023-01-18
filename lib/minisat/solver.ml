open Core
open Minisat
open Common

module type SolverType = sig
  type result = (SAT.Problem.solution, Error.t) Result.t

  val solve: ?print_sol:bool -> SAT.Problem.t -> result
  val incremental_solve:  ?print_sol:bool -> SAT.Problem.t -> SAT.Problem.incsol
end

module Make (Config: Config.ConfigType): SolverType = struct
  let config = Config.config

  module Debug = Debug.Make (val Debug.Config.(if config.verbose then enable else disable))

  type result = (SAT.Problem.solution, Error.t) Result.t

  let rec check_sat ?(print_sol=false) ?(solver=create ()) ?(lits = Hashtbl.Poly.create ~size:0 ~growth_allowed:true ()) cnf =
    Minisat.set_verbose solver 0;
    let cnt = ref 1 in
    List.iter (SAT.Problem.to_list cnf) ~f:(fun (negatives, positives) ->
        let mk_lit_sub = List.iter ~f:(fun var ->
            if Hashtbl.Poly.mem lits var then () else
              let new_lit = Lit.make !cnt in
              incr cnt;
              Hashtbl.Poly.add_exn lits ~key:var ~data:new_lit) in
        mk_lit_sub negatives; mk_lit_sub positives);
    let solution =
      try
        List.iter ~f:(fun (negatives, positives) ->
            let clause = List.map ~f:(fun neg -> Lit.neg @@ Hashtbl.Poly.find_exn lits neg) negatives
                         @ List.map ~f:(fun pos -> Hashtbl.Poly.find_exn lits pos) positives in
            add_clause_l solver clause) (SAT.Problem.to_list cnf);
        Minisat.solve solver;
        let assignment = Hashtbl.Poly.fold lits ~init:[] ~f:(fun ~key:var ~data:lit acc ->
            let asgn = match value solver lit with
              | V_true -> true | V_false -> false | _ -> assert false in
            (var, asgn)::acc) in
        let reduced_assignment = if config.dim_reduction then SAT.Problem.minimize_core_cnf cnf assignment else assignment in
        if config.dim_reduction then Debug.print @@ lazy (Printf.sprintf "minisat: #vars reduced %d -> %d" (List.length assignment) (List.length reduced_assignment));
        SAT.Problem.IncSat (reduced_assignment, check_sat ~solver:solver ~lits)
      with Minisat.Unsat -> SAT.Problem.IncUnsat
    in
    if print_sol then print_endline (SAT.Problem.str_of_incsol solution);
    solution

  let solve ?(print_sol=false) cnf =
    match check_sat ~print_sol:print_sol cnf with
    | SAT.Problem.IncSat (assigns, _) -> Ok (SAT.Problem.Sat assigns)
    | SAT.Problem.IncUnsat -> Ok (SAT.Problem.Unsat)

  let incremental_solve ?(print_sol=false) cnf =
    check_sat ~print_sol:print_sol cnf

end


