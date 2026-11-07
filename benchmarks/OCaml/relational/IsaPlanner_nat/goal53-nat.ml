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


type list = Nil | Cons of nat * list

let rec count n l =
  match l with
  | Nil -> Z
  | Cons(x, xs) ->
    if n = x then plus (S Z) (count n xs)
    else count n xs

let rec ins i l =
  match l with
  | Nil -> Cons(i, Nil)
  | Cons(x, y) ->
    if less i x then Cons(i, Cons(x, y))
    else Cons(x, ins i y)

let rec sort l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) -> ins x (sort xs)

let main x l =
  assert(count x l = count x (sort l))

[@@@types
"count :: (t1: nat) -> (t2: list) -> {t3: nat | count[0:2](t1, t2, t3) }
"]
