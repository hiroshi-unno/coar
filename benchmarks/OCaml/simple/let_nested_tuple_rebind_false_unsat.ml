(* ((a, b), c) = ((old c, old a), old b) = ((x + 2, x), x + 1), so a - b = 2. *)
let f (x : int) =
  let a = x in
  let b = x + 1 in
  let c = x + 2 in
  let ((a, b), c) = ((c, a), b) in
  a - b + (c - c)
[@@@assert "typeof(f) <: int -> { r : int | r = -2 }"]
