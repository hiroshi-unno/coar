(* The false twin of parametric_datatype_two_instances_sat.ml: the total
   length is 1, not 2. *)
type 'a lst = Nil | Cons of 'a * 'a lst

let rec len l = match l with Nil -> 0 | Cons (_, t) -> 1 + len t
let rec len2 (l : int lst lst) = match l with Nil -> 0 | Cons (x, t) -> len x + len2 t
let main n = assert (len2 (Cons (Cons (n, Nil), Nil)) = 2)

[@@@assert "typeof(main) <: int -> unit"]
