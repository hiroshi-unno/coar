(* A file's own [list] type hides the built-in one, as in OCaml. *)
type list = Nil | Cons of int * list

let rec length l = match l with Nil -> 0 | Cons (_, t) -> 1 + length t
let main l = assert (length l >= 0)

[@@@assert "typeof(main) <: list -> unit"]
