type list = Nil | Cons of int * list

let rec count n l =
  match l with
  | Nil -> 0
  | Cons(x, xs) ->
    if n = x then 1 + count n xs
    else count n xs

let rec ins i l =
  match l with
  | Nil -> Cons(i, Nil)
  | Cons(x, y) ->
    if i < x then Cons(i, Cons(x, y))
    else Cons(x, ins i y)

let rec sort l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) -> ins x (sort xs)

let main x l =
  assert(count x l = count x (sort l))

[@@@types
"count :: (t1: int) -> (t2: list) -> {t3: int | count[0:2](t1, t2, t3) && t3 >= 0}
"]
