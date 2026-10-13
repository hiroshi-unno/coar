(* Reordering parallel bindings must preserve which definition owns its bound. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let marker = (fun x -> x + 1) 0 and b = identity zero
let run n = b (n + marker) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
