type list = Nil | Cons of int * list

let rec drop n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Cons(x, xs)
    else drop (n - 1) xs

let rec take n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Nil
    else Cons(x, take (n - 1) xs)

let rec minus n m =
  if n <= m then 0
  else n - m

let main n m xs =
  if n >= 0 && m >= 0 then
    assert(drop n (take m xs) = take (minus m n) (drop n xs))
  else ()
