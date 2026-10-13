(* A new group member shadows a scalar from the preceding environment. *)
[@@@mode "hfl_prop_as_expectation"]
let marker = (fun x -> x + 10) 0
let identity f = f
let rec zero n k = zero n k
let b = identity zero and marker = (fun x -> x + 1) 0
let run n = b (n + marker) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
