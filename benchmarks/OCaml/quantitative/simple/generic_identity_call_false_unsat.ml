(* A zero-valued result cannot satisfy the positive lower bound. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let zero n k = 0.0
let b = identity zero
let run n = b n (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | 1.0 <= ret }"]
