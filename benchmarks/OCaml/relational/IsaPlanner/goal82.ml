type list = Nil | Cons of int * list

let rec append l ys =
  match l with
  | Nil -> ys
  | Cons(x, xs) ->
    Cons(x, append xs ys)

let rec take n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Nil
    else Cons(x, take (n - 1) xs)

let rec minus n m =
  if n <= m then 0
  else n - m

let rec len l =
  match l with
  | Nil -> 0
  | Cons(x, xs) -> 1 + len xs

let main n xs ys =
  if n >= 0 then
    assert(take n (append xs ys) = append (take n xs) (take (minus n (len xs)) ys))
  else ()

[@@@types
"len :: (t1: list) -> {t2: int | len[0:1](t1, t2) && t2 >= 0}
"]
