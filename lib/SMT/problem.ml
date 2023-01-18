open Ast

type t = LogicOld.Formula.t

type solution =
  | Sat of LogicOld.model
  | Unsat
  | Unknown

type incsol =
  | IncSat of LogicOld.model * (t -> incsol)
  | IncUnsat of (t -> incsol)
  | IncUnknown of (t -> incsol)

let str_of_solution = function
  | Sat model -> "sat\nmodel: " ^ LogicOld.str_of_model model
  | Unsat     -> "unsat"
  | Unknown   -> "unknown"

