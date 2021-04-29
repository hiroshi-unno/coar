open Core

val from_file: string -> (Problem.t, Error.t) result
val from_string: string -> (Problem.t, Error.t) result
val formula_from_string: string -> (Ast.LogicOld.Formula.t, Error.t) result