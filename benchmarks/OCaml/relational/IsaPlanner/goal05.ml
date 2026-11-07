type list = Nil | Cons of int * list

let rec count n l =
  match l with
  | Nil -> 0
  | Cons(x, xs) ->
    if n = x then 1 + count n xs
    else count n xs

let succ x = 1 + x

let main n x l =
  if n = x then
    let r1 = count n (Cons(x, l)) in
    assert(1 + count n l = r1)
  else ()

[@@@types
"count :: (t1: int) -> (t2: list) -> {t3: int | count[0:2](t1, t2, t3) && t3 >= 0}
"]
