(* An alias used in a [when] guard: the first case is taken exactly when the
   argument is [A 3], and then [f] returns 3, so the assertion fails at
   [n = 3]. *)
type t = A of int | B

let f x = match x with A n as y when y = A 3 -> n | A _ -> 1 | B -> 0
let main n = assert (f (A n) <> 3)

[@@@assert "typeof(main) <: int -> unit"]
