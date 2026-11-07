(* A sibling selecting a function by a computed condition. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let flag = (fun x -> x > 0) 1
let b = identity zero and keep = if flag then (fun (x : int) -> x) else (fun (x : int) -> x + 1)
let run n = b (keep n) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
