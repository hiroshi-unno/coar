open Core
open Ast.Logic
open Common.Combinator

type t = HOSAT of term

let make t = HOSAT t
let of_sat = SAT.Problem.term_of ~quant:true >> make
let of_dqsat = DQSAT.Problem.term_of ~quant:true >> make

let from_hosat_file filename =
  let ic = In_channel.create ~binary:false filename in
  let phi =
    Ast.RtypeParser.formula Ast.RtypeLexer.token @@ Lexing.from_channel ic
  in
  (*print_endline @@ Ast.LogicOld.Formula.str_of phi;*)
  let res = make @@ ExtTerm.of_old_formula phi in
  In_channel.close ic;
  res

let term_of (HOSAT t) = t
let str_of _ = failwith "not implemented"

type solution = Sat | Unsat | Unknown

let str_of_solution = function
  | Sat -> "sat"
  | Unsat -> "unsat"
  | Unknown -> "unknown"
