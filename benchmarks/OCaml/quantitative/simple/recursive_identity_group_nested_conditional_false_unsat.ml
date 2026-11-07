(* The function a nested literal conditional selects fails its assertion when called. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let b = identity zero and keep = if true then (if false then (fun (x : int) -> x + 1) else (fun (x : int) -> assert false; x)) else (fun (x : int) -> x)
let run n = b (keep n) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
