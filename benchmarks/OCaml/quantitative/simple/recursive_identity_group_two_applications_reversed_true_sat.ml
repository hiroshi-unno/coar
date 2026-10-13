(* Reverse the group order while preserving both schemes and their shared argument. *)
[@@@mode "hfl_prop_as_expectation"]

let identity f = f
let rec zero n k = zero n k

let other = identity zero
and b = identity zero

let run n = b n (fun _ -> other n (fun _ -> 0.0))

[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
