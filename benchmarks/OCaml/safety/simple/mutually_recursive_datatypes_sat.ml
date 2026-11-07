(* The true twin of mutually_recursive_datatypes_unsat.ml: a value built with
   the second member's constructor [Pair] is a [Br], and matching the [Pair]
   inside it gives back its first component. *)
type a = Leaf of int | Br of b
and b = Pair of a * a

let f x = match x with Leaf n -> n | Br p -> ( match p with Pair (l, _) -> ( match l with Leaf m -> m | Br _ -> 0))
let main n = assert (f (Br (Pair (Leaf n, Leaf 0))) = n && f (Leaf n) = n)

[@@@assert "typeof(main) <: int -> unit"]
