
type list = Nil | Cons of int * list

let rec rev acc l =
  match l with
  | Nil -> acc
  | Cons(x, xs) ->
    rev (Cons(x, acc)) xs


let main l =
  assert (rev Nil (rev Nil l) = l)
