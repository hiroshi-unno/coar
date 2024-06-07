open Core

type t

val make : (Ident.tvar * Z.t) list -> Z.t -> t
val of_z : Z.t -> t
val of_var : Ident.tvar -> t
val ( + ) : t -> t -> t
val ( ~- ) : t -> t
val ( - ) : t -> t -> t
val mult : Z.t -> t -> t
val to_string : t -> string
val ( = ) : t -> t -> bool
val compare : t -> t -> int
val vars : t -> Ident.tvar list
val coeffs : t -> Z.t list
val get_coeff_of : Ident.tvar -> t -> Z.t option
val remove : Ident.tvar -> t -> t
val eval : ?default_value:Z.t option -> (Ident.tvar, Z.t) Map.Poly.t -> t -> Z.t
val term_of : t -> Logic.term
val of_term : Logic.term -> t option
