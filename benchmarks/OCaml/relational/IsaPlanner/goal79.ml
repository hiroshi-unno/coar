type list = Nil | Cons of int * list

let leq x y = x <= y

let rec ins i l =
  match l with
  | Nil -> Cons(i, Nil)
  | Cons(x, y) ->
    if i < x then Cons(i, Cons(x, y))
    else Cons(x, ins i y)

let rec sorted l =
  match l with
  | Nil -> true
  | Cons(x, xs) ->
    match xs with
    | Nil -> true
    | Cons(y, ys) -> (leq x y) && sorted xs

let main x l =
  if sorted l then
    assert(sorted (ins x l))
  else ()

