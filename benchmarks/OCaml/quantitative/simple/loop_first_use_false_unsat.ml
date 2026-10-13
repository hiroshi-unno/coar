[@@@mode "hfl_prop_as_expectation"]

(* The false lower bound 1 on [loop] (value 0) at its only instance, which
   kept its admissible kind even before copies of an instance's unknowns
   carried their kind; the control for the same bound on a second
   instance. *)
let rec loop n k = 0.0 +. loop n k

let b = loop
[@@@assert "typeof(b) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | 1.0 <= ret }"]
