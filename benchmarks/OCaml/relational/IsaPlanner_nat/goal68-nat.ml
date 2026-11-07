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

let succ x = plus (S Z) x

let rec minus n m =
  if leq n m then Z
  else minus n m

let rec len l =
  match l with
  | Nil -> Z
  | Cons(x, xs) -> plus (S Z) (len xs)

let rec butlast l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if xs = Nil then Nil
    else Cons(x, butlast xs)

let main xs ys =
  assert(len (butlast xs) = minus (len xs) (succ Z))

[@@@types
"len :: (t1: list) -> {t2: nat | len[0:1](t1, t2) }
"]
