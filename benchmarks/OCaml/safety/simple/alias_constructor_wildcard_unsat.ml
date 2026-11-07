(* An alias over a constructor pattern matches only that constructor: the
   first case of [f] does not match [B], so [f B = 0] and the assertion fails.
   Reading [(A _ as y)] as the bare variable [y] makes the first case match
   every value and proves the assertion. *)
type t = A of int | B

let f x = match x with A _ as y -> 1 | B -> 0
let main () = assert (f B = 1)

[@@@assert "typeof(main) <: unit -> unit"]
