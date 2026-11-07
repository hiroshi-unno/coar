type list = Nil | Cons of int * list

let succ x = 1 + x

let rec minus n m =
  if n <= m then 0
  else n - m

let rec len l =
  match l with
  | Nil -> 0
  | Cons(x, xs) -> 1 + len xs

let rec butlast l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if xs = Nil then Nil
    else Cons(x, butlast xs)

let main xs ys =
  assert(len (butlast xs) = minus (len xs) (succ 0))

[@@@types
"len :: (t1: list) -> {t2: int | len[0:1](t1, t2) && t2 >= 0}
"]
