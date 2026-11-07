(* Two mutually recursive functions over two mutually recursive datatypes:
   [sa] and [sb] sum the integer leaves, so a pair of two leaves [n] sums to
   [n + n].  The solution has to relate the result to the leaves two
   constructors below the argument, as in tree_leaf_sum_sat.ml, which is the
   same program over one datatype. *)
type a = Leaf of int | Br of b
and b = Pair of a * a

let rec sa x = match x with Leaf n -> n | Br p -> sb p
and sb p = match p with Pair (l, r) -> sa l + sa r

let main n = assert (sa (Br (Pair (Leaf n, Leaf n))) = n + n)

[@@@assert "typeof(main) <: int -> unit"]
