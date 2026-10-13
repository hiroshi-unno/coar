(* Identity preserves the zero least expectation of this diverging recursion. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec loop n k = loop n k
let b = identity loop
[@@@assert "typeof(b) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | ret <= 1.0 }"]
