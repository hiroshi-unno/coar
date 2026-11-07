type nat = Z | S of nat
let rec plus m n =
  match m with
  | Z -> n
  | S m' -> S (plus m' n)
let rec minus n m =
  match n with
  | Z -> Z
  | S n' ->
    match m with
    | Z -> n
    | S m' -> minus n' m'

type list = Nil | Cons of int * list
let succ x = plus (S Z) x

let rec count n l =
  match l with
  | Nil -> Z
  | Cons(x, xs) ->
    if n = x then plus (S Z) (count n xs)
    else count n xs

let main n l =
  assert(plus (S Z) (count n l) = count n (Cons(n, l)))

[@@@types
"count :: (t1: int) -> (t2: list) -> {t3: nat | count[0:2](t1, t2, t3) }
"]

