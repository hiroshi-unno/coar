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
let rec less x y =
  match y with
  | Z -> false
  | S y' ->
    match x with
    | Z -> true
    | S x' -> less x' y'
let leq x y =
  x = y || less x y

type list = Nil | Cons of int * list

let rec append l ys =
  match l with
  | Nil -> ys
  | Cons(x, xs) ->
    Cons(x, append xs ys)

let rec count n l =
  match l with
  | Nil -> Z
  | Cons(x, xs) ->
    if n = x then plus (S Z) (count n xs)
    else count n xs

let main n l m =
  let s1 = count n l in
  let s2 = append l m in
  let s3 = count n s2 in
  assert(leq s1 s3)


[@@@types
"count :: (t1: int) -> (t2: list) -> {t3: nat | count[0:2](t1, t2, t3)}"]

(* [@@@option "-extract-entailment -induct-limit=1"] *)
