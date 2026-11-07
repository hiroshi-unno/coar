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

let rec append l ys =
  match l with
  | Nil -> ys
  | Cons(x, xs) ->
    Cons(x, append xs ys)

let main x l =
  assert(mem x (ins x l))
