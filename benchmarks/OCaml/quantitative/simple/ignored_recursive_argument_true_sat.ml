(* The recursive argument is unused; the returned function computes one. *)
[@@@mode "hfl_prop_as_expectation"]
let ignore_argument f = fun (n : int) (k : int -> float) -> 1.0
let rec zero n (k : int -> float) = zero n k
let b = ignore_argument zero
[@@@assert "typeof(b) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | 1.0 <= ret }"]
