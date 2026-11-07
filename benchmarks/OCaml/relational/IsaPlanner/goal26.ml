type list = Nil | Cons of int * list

let rec mem x l =
  match l with
  | Nil -> false
  | Cons(y, ys) ->
    x = y || mem x ys

let rec append l ys =
  match l with
  | Nil -> ys
  | Cons(x, xs) ->
    Cons(x, append xs ys)

let main x l t =
  if mem x l then
    assert(mem x (append l t))
  else ()
