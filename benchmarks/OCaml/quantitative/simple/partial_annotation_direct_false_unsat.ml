(* The least nonnegative expectation of this nonterminating recursion is zero. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n (k : int -> float) = zero n k
let b = zero
[@@@assert "typeof(b) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | 1.0 <= ret }"]
