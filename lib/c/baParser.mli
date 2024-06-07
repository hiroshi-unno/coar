open Ast.LogicOld
open CSyntax

val from_file : string -> (Formula.t BuchiAutomaton.t, string) result
val from_string : string -> (Formula.t BuchiAutomaton.t, string) result
