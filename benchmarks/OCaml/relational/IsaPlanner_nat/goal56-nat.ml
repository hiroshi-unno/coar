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

let rec len l =
  match l with
  | Nil -> Z
  | Cons(x, xs) -> plus (S Z) (len xs)

let rec drop n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = Z then Cons(x, xs)
    else drop (minus n (S Z)) xs

let rec append l ys =
  match l with
  | Nil -> ys
  | Cons(x, xs) ->
    Cons(x, append xs ys)

let main n xs ys =
  assert(drop n (append xs ys) = append (drop n xs) (drop (minus n (len xs)) ys))

[@@@types
  "len :: (t1: list) -> {t2: nat | len[0:1](t1, t2) }
"]
