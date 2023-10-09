open Core

val from_file: print:(string lazy_t -> unit) -> string -> (Problem.t, Error.t) result
val from_string: print:(string lazy_t -> unit) -> string -> (Problem.t, Error.t) result
val formula_from_string: print:(string lazy_t -> unit) -> string -> (Ast.LogicOld.Formula.t, Error.t) result