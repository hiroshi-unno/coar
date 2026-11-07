(* Every division and [mod] here has a divisor that is non-zero on the path
   reaching it, so none raises Division_by_zero; OCaml truncates toward zero,
   so [-7 / 2 = -3] and [-7 mod 2 = -1]. *)
let f (x : int) = if x = 0 then 0 else 10 / x
let g (x : int) = 100 mod (abs x + 1)
let h (n : int) = if n < 0 then (n / 2) + (n mod 2) else n
[@@@assert "typeof(f) <: int -> int"]
[@@@assert "typeof(g) <: int -> { r : int | 0 <= r }"]
[@@@assert "typeof(h) <: { n : int | n = -7 } -> { r : int | r = -4 }"]
