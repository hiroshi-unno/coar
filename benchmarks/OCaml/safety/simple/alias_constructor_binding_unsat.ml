(* As alias_constructor_binding_sat.ml with the result off by one: [f (A n)]
   is 1, so the assertion fails. *)
type t = A of int | B

let f x =
  match x with A n as y -> ( match y with A m -> m - n + 1 | B -> 0) | B -> 0

let main n = assert (f (A n) = 0)

[@@@assert "typeof(main) <: int -> unit"]
