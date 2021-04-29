type key
type elem

type ('a, 'b) t = ('a * 'b) list

val str_of_tenv: (Ident.tvar, 'b) t -> string
val str_of_penv: (Ident.pvar, 'b) t -> string
val lookupi_exn: 'a -> ('a, 'b) t -> 'b * int
val lookup_exn: 'a -> ('a, 'b) t -> 'b
val lookupi: 'a -> ('a, 'b) t -> ('b * int) option
val lookup: 'a -> ('a, 'b) t -> 'b option
val update: ('a * 'b) list -> ('a, 'b) t -> ('a, 'b) t
val keys: ('a, 'b) t -> 'a list
val elems: ('a, 'b) t -> 'b list
val entries: ('a, 'b) t -> ('a * 'b) list
val nth: ('a, 'b) t -> int -> 'a * 'b
val length: ('a, 'b) t -> int
val size: ('a, 'b) t -> int
val has: 'a -> ('a, 'b) t -> bool
val empty: ('a, 'b) t
