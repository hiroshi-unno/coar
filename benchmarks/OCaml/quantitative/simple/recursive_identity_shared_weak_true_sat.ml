(* The argument type is shared with an earlier weakly polymorphic identity. *)
[@@@mode "hfl_prop_as_expectation"]
let shared = (fun f -> f) (fun x -> x)
let identity f = f
let rec zero n k = zero n k
let b = identity zero
let run n = b (shared n) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
