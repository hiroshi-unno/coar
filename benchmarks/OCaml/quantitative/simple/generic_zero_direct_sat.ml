(* Identity must preserve zero's true upper bound. Generic and
   explicitly typed identity applications currently fail at different
   frontend instantiation boundaries; zero directly is the sat control. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let zero n k = 0.0
[@@@assert "typeof(zero) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | ret <= 1.0 }"]
