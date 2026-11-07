(* OCaml's [mod] raises Division_by_zero when the divisor is 0, as [/] does,
   and the exception escapes [g]. *)
let g (x : int) (y : int) = x mod y
[@@@assert "typeof(g) <: int -> int -> int"]
