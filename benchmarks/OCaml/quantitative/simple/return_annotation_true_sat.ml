(* Annotations and application forms isolate the higher-order instantiation boundary. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let zero n k = 0.0
let b : int -> (int -> float) -> float = identity zero
[@@@assert "typeof(b) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | ret <= 1.0 }"]
