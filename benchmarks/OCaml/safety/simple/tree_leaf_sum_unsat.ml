(* The false twin of tree_leaf_sum_sat.ml: a node over two leaves [n] sums to
   [n + n], which is [n] only at [n = 0]. *)
type a = Leaf of int | Br of a * a

let rec sa x = match x with Leaf n -> n | Br (l, r) -> sa l + sa r

let main n = assert (sa (Br (Leaf n, Leaf n)) = n)

[@@@assert "typeof(main) <: int -> unit"]
