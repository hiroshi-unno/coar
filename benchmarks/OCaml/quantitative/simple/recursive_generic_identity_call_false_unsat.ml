(* The least nonnegative expectation of this nonterminating recursion is zero. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let b = identity zero
let run n = b n (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | 1.0 <= ret }"]
