(* The recursive result is a type variable until this assertion.
   Its expectation is the least fixed point of the identity, hence zero.
   The assertion's instantiation must impose admissibility just like an
   expression use. The false lower bound used to be reported sat,0. *)
[@@@mode "hfl_prop_as_expectation"]
let rec loop n k = loop n k
[@@@assert "typeof(loop) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | ret <= 1.0 }"]
