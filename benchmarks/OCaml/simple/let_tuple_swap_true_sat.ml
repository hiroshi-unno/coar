(* The pair binding swaps a and b simultaneously: a - b goes from -1 to 1. *)
let f (x : int) =
  let a = x in
  let b = x + 1 in
  let (a, b) = (b, a) in
  a - b
[@@@assert "typeof(f) <: int -> { r : int | r = 1 }"]
