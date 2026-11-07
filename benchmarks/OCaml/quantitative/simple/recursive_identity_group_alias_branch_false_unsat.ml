(* The selected alias branch names a function whose assertion fails when called. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let keep0 (x : int) = assert false; x
let b = identity zero and keep = if true then keep0 else (fun (x : int) -> x)
let run n = b (keep n) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
