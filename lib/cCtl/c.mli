open Core

val from_file: string -> (MuCLP.Problem.t, Error.t) result
val from_string: string -> (MuCLP.Problem.t, Error.t) result
