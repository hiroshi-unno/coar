(* A false lower bound through a polymorphic-sibling group must not verify. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let b = identity zero and id2 x = x
let run n = b (id2 (n + 0)) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | 1.0 <= ret }"]
