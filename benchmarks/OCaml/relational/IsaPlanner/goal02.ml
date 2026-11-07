type list = Nil | Cons of int * list

let rec append l ys =
  match l with
  | Nil -> ys
  | Cons(x, xs) ->
    Cons(x, append xs ys)

let rec count n l =
  match l with
  | Nil -> 0
  | Cons(x, xs) ->
    if n = x then 1 + count n xs
    else count n xs

let main n l m =
  assert(count n l + count n m = count n (append l m))

[@@@types
"append :: (t1: list) -> (t2: list) -> {t3: list | append[0:2](t1, t2, t3)}
 count :: (t1: int) -> (t2: list) -> {t3: int | count[0:2](t1, t2, t3) && t3 >= 0}"]
