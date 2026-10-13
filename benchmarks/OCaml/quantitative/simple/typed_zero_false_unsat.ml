(* A function returning zero cannot satisfy a positive lower bound. *)
[@@@mode "hfl_prop_as_expectation"]
let zero (n : int) (k : int -> float) = 0.0
[@@@assert "typeof(zero) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | 1.0 <= ret }"]
