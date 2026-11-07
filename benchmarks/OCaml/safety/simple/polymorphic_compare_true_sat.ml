(* A comparison at a type variable inside a polymorphic function: [le] is
   checked at its type ['a -> 'a -> bool] before it is generalised, where
   [x <= y] is an ordering with no theory until ['a] is instantiated. *)
let le x y = x <= y

let main (a:int) = assert (le a a)

[@@@assert "typeof(main) <: int -> unit"]
