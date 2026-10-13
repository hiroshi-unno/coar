[@@@mode "hfl_prop_as_expectation"]

(* The control for the false lower bound on the second instance: [loop]'s
   value is 0, so the upper bound 1 on [b], [loop]'s second instance, is true
   and provable with an admissible return refinement. *)
let rec loop n k = 0.0 +. loop n k

let a = loop

let b = loop
[@@@assert "typeof(b) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | ret <= 1.0 }"]
