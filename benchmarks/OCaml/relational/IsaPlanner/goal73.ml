type list = Nil | Cons of int * list

let rec mem x l =
  match l with
  | Nil -> false
  | Cons(y, ys) ->
    x = y || mem x ys

let rec ins i l =
  match l with
  | Nil -> Cons(i, Nil)
  | Cons(x, y) ->
    if i < x then Cons(i, Cons(x, y))
    else Cons(x, ins i y)

let main x y l =
  if x <> y then
    assert(mem x (ins y l) = mem x l)
  else ()

