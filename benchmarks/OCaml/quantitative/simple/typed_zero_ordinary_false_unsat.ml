(* A function returning zero cannot satisfy a positive lower bound. *)
let zero (n : int) (k : int -> float) = 0.0
[@@@assert "typeof(zero) <: int -> (int -> { r : float | r = 0.0 }) -> { ret : float | 1.0 <= ret }"]
