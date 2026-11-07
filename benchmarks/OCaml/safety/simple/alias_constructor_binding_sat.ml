(* An alias binds the whole matched value while the pattern under it binds its
   parts: [y] is [A n], so matching it again gives [m = n]. *)
type t = A of int | B

let f x =
  match x with A n as y -> ( match y with A m -> m - n | B -> 1) | B -> 0

let main n = assert (f (A n) = 0 && f B = 0)

[@@@assert "typeof(main) <: int -> unit"]
