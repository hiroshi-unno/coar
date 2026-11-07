(* A literal conditional whose branches are aliases of a preceding function. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let keep0 (x : int) = x
let b = identity zero and keep = if true then keep0 else keep0
let run n = b (keep n) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
