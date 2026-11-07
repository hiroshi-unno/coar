(* One parametric datatype used at two element types, [int lst] and
   [int lst lst]: each instance's size counts different fields (an [int] head
   counts nothing, an [int lst] head its own size), so a size function shared
   by name between the two would be defined twice.  The outer list holds one
   one-element list, whose length is 1. *)
type 'a lst = Nil | Cons of 'a * 'a lst

let rec len l = match l with Nil -> 0 | Cons (_, t) -> 1 + len t
let rec len2 (l : int lst lst) = match l with Nil -> 0 | Cons (x, t) -> len x + len2 t
let main n = assert (len2 (Cons (Cons (n, Nil), Nil)) = 1)

[@@@assert "typeof(main) <: int -> unit"]
