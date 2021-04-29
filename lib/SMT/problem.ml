open Ast

type t = LogicOld.Formula.t

type solution =
  | Sat of ((Ident.tvar * LogicOld.Sort.t) * LogicOld.Term.t option) list
  | Unsat
  | Unknown

type incsol = 
  | IncSat of ((Ident.tvar * LogicOld.Sort.t) * LogicOld.Term.t option) list * (t -> incsol) 
  | IncUnsat of (t -> incsol)
  | IncUnknown of (t -> incsol)

let str_of_solution = function
  | Sat model -> "sat\nmodel: " ^ LogicOld.TermSubst.str_of_model model
  | Unsat     -> "unsat"
  | Unknown   -> "unknown"

