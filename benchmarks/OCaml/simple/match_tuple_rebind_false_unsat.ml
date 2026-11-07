(* The pattern rebinds a to the old b: (a, c) = (x + 1, x), so a - c = 1. *)
let f (x : int) =
  let a = x in
  let b = x + 1 in
  match (b, a) with (a, c) -> a - c
[@@@assert "typeof(f) <: int -> { r : int | r = -1 }"]
