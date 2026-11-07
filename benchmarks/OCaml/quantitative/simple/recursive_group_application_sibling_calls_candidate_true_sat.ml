(* A recursive function of the group calls the application, so the two share its result rank; the application is also used after the group. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let rec go n = b n (fun _ -> 0.0) and b = identity zero
let run n = b n (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
