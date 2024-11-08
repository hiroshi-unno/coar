open Core

val muclp_from_file :
  print:(string lazy_t -> unit) -> string -> (Problem.t, Error.t) result

val muclp_from_string :
  print:(string lazy_t -> unit) -> string -> (Problem.t, Error.t) result

val query_from_string :
  print:(string lazy_t -> unit) ->
  string ->
  (Ast.LogicOld.Formula.t, Error.t) result
