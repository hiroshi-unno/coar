(* A function sibling shadows a function of the preceding environment. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let keep (x : int) = x
let b = identity zero and keep (x : int) = x + 1
let run n = b (keep n) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
