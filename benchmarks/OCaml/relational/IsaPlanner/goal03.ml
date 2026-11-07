type list = Nil | Cons of int * list

let leq x y = x <= y

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
  let s1 = count n l in
  let s2 = append l m in
  let s3 = count n s2 in
  assert(leq s1 s3)


[@@@types
"count :: (t1: int) -> (t2: list) -> {t3: int | count[0:2](t1, t2, t3) && t3 >= 0}"]
