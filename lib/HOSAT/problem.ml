(* Higher-order Boolean satisfiability problems: one closed Boolean term of
   [Ast.Logic], whose quantifiers may range over Boolean functions.  A SAT or
   DQBF problem is embedded by [of_sat]/[of_dqsat] (its free variables closed
   existentially), and a [.hosat] file is read with the refinement-type
   formula grammar.  The higher-order model-checking backend decides it. *)
open Core
open Ast.Logic
open Common.Combinator

type t = HOSAT of term

let make t = HOSAT t
let of_sat = SAT.Problem.term_of ~quant:true >> make
let of_dqsat = DQSAT.Problem.term_of ~quant:true >> make

let from_hosat_file filename =
  In_channel.with_file ~binary:false filename ~f:(fun ic ->
      let phi =
        Ast.RtypeParser.formula Ast.RtypeLexer.token @@ Lexing.from_channel ic
      in
      (*print_endline @@ Ast.LogicOld.Formula.str_of phi;*)
      make @@ ExtTerm.of_old_formula phi)

let term_of (HOSAT t) = t
let str_of _ = failwith "not implemented"

type solution = Sat | Unsat | Unknown

let str_of_solution = function
  | Sat -> "sat"
  | Unsat -> "unsat"
  | Unknown -> "unknown"
