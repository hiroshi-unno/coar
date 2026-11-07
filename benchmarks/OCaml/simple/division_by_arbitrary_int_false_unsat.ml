(* OCaml's [/] raises Division_by_zero when the divisor is 0, and the
   exception escapes [f]: [f 0] fails, so [f] does not have type [int -> int]. *)
let f (x : int) = 10 / x
[@@@assert "typeof(f) <: int -> int"]
