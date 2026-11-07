(* One recursive function over one binary datatype, summing the integer
   leaves: a node over two leaves [n] sums to [n + n].  The one-datatype
   counterpart of mutually_recursive_functions_leaf_sum_sat.ml. *)
type a = Leaf of int | Br of a * a

let rec sa x = match x with Leaf n -> n | Br (l, r) -> sa l + sa r

let main n = assert (sa (Br (Leaf n, Leaf n)) = n + n)

[@@@assert "typeof(main) <: int -> unit"]
