(* The MiniSat backend for CNF satisfiability, one-shot and incremental.

   [incremental_solve] returns, with a model, a continuation that adds more
   clauses to the same MiniSat instance; variable names are mapped to MiniSat
   literals by a table the continuation keeps, so a name means the same
   variable across every call of one chain.  [solve] is the first call of such
   a chain with the continuation dropped. *)
open Core
open Minisat
open Common
open Common.Combinator

module type SolverType = sig
  val solve :
    ?print_sol:bool -> SAT.Problem.t -> SAT.Problem.solution Or_error.t

  val incremental_solve : ?print_sol:bool -> SAT.Problem.t -> SAT.Problem.incsol
end

module Make (Config : Config.ConfigType) : SolverType = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let rec check_sat ?(print_sol = false) ?(solver = create ())
      ?(lits = Hashtbl.Poly.create ~size:0 ~growth_allowed:true ()) cnf =
    Minisat.set_verbose solver 0;
    (* The next unused literal number, and it must continue where the previous
       call stopped: the continuation this function returns keeps both the
       solver and [lits], so a later call that mentions a variable for the first
       time needs a number nobody holds.  Restarting at 1 gave that variable the
       number an earlier call had already given to another one, silently making
       two variables one -- adding [not b] to [a] then came back unsat although
       [a and not b] is satisfiable.  [lits] only grows and hands out 1, 2, ...
       in order, so its size is exactly how far the numbering has got. *)
    let cnt = ref (Hashtbl.Poly.length lits + 1) in
    List.iter (SAT.Problem.clauses_of cnf) ~f:(fun (negatives, positives) ->
        let mk_lit_sub =
          List.iter ~f:(fun var ->
              if Hashtbl.Poly.mem lits var then ()
              else
                let new_lit = Lit.make !cnt in
                incr cnt;
                Hashtbl.Poly.add_exn lits ~key:var ~data:new_lit)
        in
        mk_lit_sub negatives;
        mk_lit_sub positives);
    let solution =
      try
        List.iter (SAT.Problem.clauses_of cnf) ~f:(fun (negatives, positives) ->
            let clause =
              List.map negatives ~f:(Hashtbl.Poly.find_exn lits >> Lit.neg)
              @ List.map positives ~f:(Hashtbl.Poly.find_exn lits)
            in
            add_clause_l solver clause);
        Minisat.solve solver;
        let assignment =
          Hashtbl.Poly.fold lits ~init:[] ~f:(fun ~key:var ~data:lit acc ->
              let asgn =
                match value solver lit with
                | V_true -> true
                | V_false -> false
                | _ -> assert false
              in
              (var, asgn) :: acc)
        in
        let reduced_assignment =
          if config.dim_reduction then
            SAT.Problem.minimize_core_cnf cnf assignment
          else assignment
        in
        if config.dim_reduction then
          Debug.print
          @@ lazy
               (sprintf "minisat: #vars reduced %d -> %d"
                  (List.length assignment)
                  (List.length reduced_assignment));
        SAT.Problem.IncSat (reduced_assignment, check_sat ~solver ~lits)
      with Minisat.Unsat -> SAT.Problem.IncUnsat
    in
    if print_sol then print_endline (SAT.Problem.str_of_incsol solution);
    solution

  let solve ?(print_sol = false) cnf =
    match check_sat ~print_sol cnf with
    | SAT.Problem.IncSat (assigns, _) -> Ok (SAT.Problem.Sat assigns)
    | SAT.Problem.IncUnsat -> Ok SAT.Problem.Unsat
    | SAT.Problem.IncUnknown -> Ok SAT.Problem.Unknown

  let incremental_solve ?(print_sol = false) cnf = check_sat ~print_sol cnf
end
