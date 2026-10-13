(* The false bound is unchanged when the parallel group order is reversed. *)
[@@@mode "hfl_prop_as_expectation"]

let identity f = f
let rec zero n k = zero n k

let other = identity zero
and b = identity zero

let run n = b n (fun _ -> other n (fun _ -> 0.0))

[@@@assert "typeof(run) <: int -> { ret : prop | 1.0 <= ret }"]
