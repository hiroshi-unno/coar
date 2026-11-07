(* Built when the `lp-gurobi` package is not installed (dune's [select] in this
   directory's dune file): Gurobi is commercial, so the library must build and
   run without it, and selecting it then gives an error. *)
let available = false

let solve ~term_output:_ (_ : Lp.Problem.t) :
    (float * float Lp.PMap.t, string) result =
  Error
    "MIPSolver: Gurobi is not available in this build (the lp-gurobi package \
     is not installed); select Glpk or Best_available"
