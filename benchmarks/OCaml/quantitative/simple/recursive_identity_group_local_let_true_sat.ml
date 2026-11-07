(* A sibling defined by a local let leaves the application result generic. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let b = identity zero and keep = let k = 1 in fun (x : int) -> x + k
let run n = b (keep n) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
