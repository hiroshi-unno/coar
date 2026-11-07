(* Two mutually recursive datatypes declared with [type ... and ...]: the
   constructor [Pair] belongs to [b], the second member of the group.  [f]
   returns 0 on a [Br], so the assertion fails for every [n <> 0]. *)
type a = Leaf of int | Br of b
and b = Pair of a * a

let f x = match x with Leaf n -> n | Br _ -> 0
let main n = assert (f (Br (Pair (Leaf n, Leaf n))) = n)

[@@@assert "typeof(main) <: int -> unit"]
