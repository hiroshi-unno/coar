(* The pair binding reads the old a and b: (a, c) = (x + 1, x), so a - c = 1. *)
let f (x : int) =
  let a = x in
  let b = x + 1 in
  let (a, c) = (b, a) in
  a - c
[@@@assert "typeof(f) <: int -> { r : int | r = -1 }"]
