(* The least expectation of an identity recursive equation is zero. Passing
   that function through identity must not verify a positive lower bound. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec loop n k = loop n k
let b = identity loop
[@@@assert "typeof(b) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | 1.0 <= ret }"]
