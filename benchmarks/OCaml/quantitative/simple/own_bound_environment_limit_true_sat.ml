(* The own bound mentions an earlier top-level value, which stays shared. *)
[@@@mode "hfl_prop_as_expectation"]
let limit = 10
let restrict f = fun n k -> assert (n <= limit); f n k
let rec zero n k = zero n k
let b = restrict zero
let run n = b 5 (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
