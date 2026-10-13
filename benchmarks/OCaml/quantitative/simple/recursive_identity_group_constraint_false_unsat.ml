(* The other nonrecursive group member owns an independent scalar constraint. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let b = identity zero and marker = (fun x -> x + 1) 0
let run n = b (n + marker) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | 1.0 <= ret }"]
