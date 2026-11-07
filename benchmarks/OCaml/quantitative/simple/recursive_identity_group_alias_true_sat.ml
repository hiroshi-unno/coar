(* Local alias sibling bounds remain in the enclosing assertion. *)
[@@@mode "hfl_prop_as_expectation"]

let identity f = f
let rec zero n k = zero n k

let keep0 (x : int) = x

let b = identity zero
and keep = keep0

let run n = b (keep n) (fun _ -> 0.0)

[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
