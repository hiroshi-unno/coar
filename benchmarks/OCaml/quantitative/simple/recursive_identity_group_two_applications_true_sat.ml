(* Both applications remain separate schemes even in the same parallel group. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let b = identity zero and other = identity zero
let run n = b n (fun _ -> other n (fun _ -> 0.0))
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
