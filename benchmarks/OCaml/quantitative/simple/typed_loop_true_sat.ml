(* The least nonnegative expectation of this nonterminating recursion is zero. *)
[@@@mode "hfl_prop_as_expectation"]
let rec zero (n : int) (k : int -> float) = zero n k
[@@@assert "typeof(zero) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | ret <= 1.0 }"]
