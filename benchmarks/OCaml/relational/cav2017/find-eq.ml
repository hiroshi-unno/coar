type list = Nil | Cons of int * list
type int_option = None | Some of int
type exc = Not_found

let rec find p l ok exc =
  match l with
  | Nil -> exc Not_found
  | Cons(x,l) -> if p x then ok x else find p l ok exc

let rec find_opt p l =
  match l with
  | Nil -> None
  | Cons(x,l) -> if p x then Some x else find_opt p l

let kok p l x = assert (find_opt p l = Some x)
let kex p l Not_found = assert (find_opt p l = None)
let main p l = find p l (kok p l) (kex p l)
