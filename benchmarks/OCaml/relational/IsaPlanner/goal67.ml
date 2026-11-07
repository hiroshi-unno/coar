type list = Nil | Cons of int * list

let rec len l =
  match l with
  | Nil -> 0
  | Cons(x, xs) -> 1 + len xs

let rec filter f l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if f x then Cons(x, filter f xs)
    else filter f xs

let leq x y = x <= y

let main p xs =
  assert(leq (len (filter p xs)) (len xs))
