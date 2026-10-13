(* A preceding expansive binding must retain its own refinement constraints. *)
[@@@mode "hfl_prop_as_expectation"]
let marker = (fun x -> x + 1) 0
let identity f = f
let rec zero n k = zero n k
let b = identity zero
let run n = b (n + marker) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
