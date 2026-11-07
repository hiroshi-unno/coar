type list = Nil | Cons of int * list

let rec take n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Nil
    else Cons(x, take (n - 1) xs)

let succ x = 1 + x

let main n x xs =
  if n >= 0 then
    assert(take (succ n) (Cons(x, xs)) = Cons(x, take n xs))
  else ()
