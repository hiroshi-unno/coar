(* A tuple-valued sibling leaves the application result generic. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let b = identity zero and pair = (1, 2)
let run n = b (n + (match pair with (a, _) -> a)) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
