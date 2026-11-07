type list = Nil | Cons of int * list

let rec append l ys =
  match l with
  | Nil -> ys
  | Cons(x, xs) ->
    Cons(x, append xs ys)

let rec rev l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) -> append (rev xs) (Cons(x, Nil))

let rec filter f l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if f x then Cons(x, filter f xs)
    else filter f xs

let main p xs =
  assert(rev (filter p xs) = filter p (rev xs))
