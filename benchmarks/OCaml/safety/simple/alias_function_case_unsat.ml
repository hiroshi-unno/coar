(* The same alias in a [function] case: [f B] takes the second case and is 0,
   so the assertion fails. *)
type t = A of int | B

let f = function A _ as y -> 1 | B -> 0
let main n = assert (f B = 1)

[@@@assert "typeof(main) <: int -> unit"]
