type list = Nil | Cons of int * list

let rec take n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Nil
    else Cons(x, take (n - 1) xs)

let rec drop n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Cons(x, xs)
    else drop (n - 1) xs

let main n m xs =
  if n >= 0 && m >= 0 then
    assert(take n (drop m xs) = drop m (take (n + m) xs))
  else ()
