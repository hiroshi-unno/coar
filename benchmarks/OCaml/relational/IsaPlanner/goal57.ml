type list = Nil | Cons of int * list

let rec drop n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Cons(x, xs)
    else drop (n - 1) xs

let main n m xs =
  if n >= 0 && m >= 0 then
    assert(drop n (drop m xs) = drop (n + m) xs)
  else ()
