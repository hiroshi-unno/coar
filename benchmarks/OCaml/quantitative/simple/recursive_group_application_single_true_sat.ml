(* A let rec binding an application that mentions no group member is generalized as a nonrecursive one. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let rec b = identity zero
let run n = b n (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
