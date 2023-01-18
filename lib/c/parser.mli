open Core

val from_cctl_file: string -> (MuCLP.Problem.t, Error.t) result

val from_cltl_file: string -> (MuCLP.Problem.t, Error.t) result

val parse_cctl: string -> (MuCLP.Problem.t, Error.t) result

val parse_cltl: string -> (MuCLP.Problem.t, Error.t) result
