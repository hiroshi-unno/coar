type list = Nil | Cons of int * list

let rec butlast l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if xs = Nil then Nil
    else Cons(x, butlast xs)

let rec append l ys =
  match l with
  | Nil -> ys
  | Cons(x, xs) ->
    Cons(x, append xs ys)

let main x xs =
  assert(butlast (append xs (Cons(x, Nil))) = xs)
