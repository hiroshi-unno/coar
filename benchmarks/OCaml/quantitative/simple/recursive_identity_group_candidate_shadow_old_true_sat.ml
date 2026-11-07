(* A value read before the application binding shadows it keeps its old fact, which verifies. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let b = 1
let c = b
let b = identity zero and keep (x : int) = x
let run n = assert (c = 1); b (keep n) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
