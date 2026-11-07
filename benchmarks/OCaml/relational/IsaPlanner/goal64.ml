type list = Nil | Cons of int * list

let rec drop n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Cons(x, xs)
    else drop (n - 1) xs

let less x y = x < y

let rec len l =
  match l with
  | Nil -> 0
  | Cons(x, xs) -> 1 + len xs

let rec last l =
  match l with
  | Nil -> 0
  | Cons(x, xs) ->
    if xs = Nil then x
    else last xs

let main n xs =
  if n >= 0 then
    if less n (len xs) then
      assert(last (drop n xs) = last xs)
    else ()
  else ()
