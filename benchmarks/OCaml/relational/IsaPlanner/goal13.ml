type list = Nil | Cons of int * list

let rec append l ys =
  match l with
  | Nil -> ys
  | Cons(x, xs) ->
    Cons(x, append xs ys)

let rec drop n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Cons(x, xs)
    else drop (n - 1) xs

let succ x = 1 + x

let main n x xs =
  if n >= 0 then
    assert(drop (succ n) (Cons(x, xs)) = drop n xs)
  else ()
