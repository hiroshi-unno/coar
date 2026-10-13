(* Both calls have zero least expectation; their weak arguments remain shared. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let b = identity zero
let run_a n = b n (fun _ -> 0.0)
let run_b n = b n (fun _ -> 0.0)
[@@@assert "typeof(run_a) <: int -> { ret : prop | ret <= 1.0 }"]
[@@@assert "typeof(run_b) <: int -> { ret : prop | ret <= 1.0 }"]
