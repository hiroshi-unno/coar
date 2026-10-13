(* Identity must preserve the true upper bound of an explicitly typed zero function. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let zero (n : int) (k : int -> float) = 0.0
let b = identity zero
[@@@assert "typeof(b) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | ret <= 1.0 }"]
