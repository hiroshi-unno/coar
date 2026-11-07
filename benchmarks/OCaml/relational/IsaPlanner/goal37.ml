type list = Nil | Cons of int * list

let rec mem x l =
  match l with
  | Nil -> false
  | Cons(y, ys) ->
    x = y || mem x ys

let rec delete x l =
  match l with
  | Nil -> Nil
  | Cons(y, ys) ->
    if x = y then delete x ys
    else Cons(y, delete x ys)

let main x l =
  assert(not (mem x (delete x l)))
