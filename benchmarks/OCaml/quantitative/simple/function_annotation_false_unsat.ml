(* A zero-valued result cannot satisfy the positive lower bound. *)
[@@@mode "hfl_prop_as_expectation"]
let identity (f : int -> (int -> float) -> float) = f
let zero n k = 0.0
let b = identity zero
[@@@assert "typeof(b) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | 1.0 <= ret }"]
