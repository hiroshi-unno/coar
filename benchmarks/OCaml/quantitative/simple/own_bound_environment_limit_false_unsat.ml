(* A call above the shared limit must be refuted. *)
[@@@mode "hfl_prop_as_expectation"]
let limit = 10
let restrict f = fun n k -> assert (n <= limit); f n k
let rec zero n k = zero n k
let b = restrict zero
let run n = b 11 (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
