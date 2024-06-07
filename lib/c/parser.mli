open Core

val from_cctl_file :
  print:(string lazy_t -> unit) -> string -> (MuCLP.Problem.t, Error.t) result

val from_cltl_file :
  print:(string lazy_t -> unit) -> string -> (MuCLP.Problem.t, Error.t) result

val parse_cctl :
  print:(string lazy_t -> unit) -> string -> (MuCLP.Problem.t, Error.t) result

val parse_cltl :
  print:(string lazy_t -> unit) -> string -> (MuCLP.Problem.t, Error.t) result
