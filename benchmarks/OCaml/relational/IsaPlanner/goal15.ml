type list = Nil | Cons of int * list

let rec len l =
  match l with
  | Nil -> 0
  | Cons(x, xs) -> 1 + len xs

let rec ins i l =
  match l with
  | Nil -> Cons(i, Nil)
  | Cons(x, y) ->
    if i < x then Cons(i, Cons(x, y))
    else Cons(x, ins i y)

let succ x = 1 + x

let main x l =
  assert(len (ins x l) = succ (len l))

[@@@types
"len :: (t1: list) -> {t2: int | len[0:1](t1, t2) && t2 >= 0}
"]
