type list = Nil | Cons of int * list

let succ x = 1 + x

let rec count n l =
  match l with
  | Nil -> 0
  | Cons(x, xs) ->
    if n = x then 1 + count n xs
    else count n xs

let main n l =
  assert(1 + count n l = count n (Cons(n, l)))

[@@@types
"count :: (t1: int) -> (t2: list) -> {t3: int | count[0:2](t1, t2, t3) && t3 >= 0}
"]
