type list = Nil | Cons of int * list

let rec minus n m =
  if n <= m then 0
  else n - m

let rec len l =
  match l with
  | Nil -> 0
  | Cons(x, xs) -> 1 + len xs

let rec drop n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Cons(x, xs)
    else drop (n - 1) xs

let main n xs =
  if n >= 0 then
    assert(len (drop n xs) = minus (len xs) n)
  else ()

[@@@types
"len :: (t1: list) -> {t2: int | len[0:1](t1, t2) && t2 >= 0}
"]
