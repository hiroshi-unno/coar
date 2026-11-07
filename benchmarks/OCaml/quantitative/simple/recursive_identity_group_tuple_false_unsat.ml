(* A false assertion about the tuple sibling's component is refuted. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let b = identity zero and pair = (1, 2)
let run n = assert (match pair with (a, _) -> a = 2); b (n + (match pair with (a, _) -> a)) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
