(* Built where CoAR.MIPGurobi is (the `lp-gurobi` package is installed; dune's
   [select] in this directory's dune file): the commercial Gurobi engine, with
   its license banner kept off standard output when [term_output] is false. *)
let available = true

let solve ~term_output problem =
  MIPGurobi.GurobiInterface.solve ~term_output problem
