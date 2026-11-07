(* The false twin of mutually_recursive_functions_leaf_sum_sat.ml: a pair of
   two leaves [n] sums to [n + n], which is [n] only at [n = 0]. *)
type a = Leaf of int | Br of b
and b = Pair of a * a

let rec sa x = match x with Leaf n -> n | Br p -> sb p
and sb p = match p with Pair (l, r) -> sa l + sa r

let main n = assert (sa (Br (Pair (Leaf n, Leaf n))) = n)

[@@@assert "typeof(main) <: int -> unit"]
