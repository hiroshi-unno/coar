open CSyntax
open Ast.LogicOld

val ba_of_ltl :
  print:(string lazy_t -> unit) -> Ltl.t -> Formula.t BuchiAutomaton.t

val hmes_of_ba : Formula.t BuchiAutomaton.t -> HMES.t
