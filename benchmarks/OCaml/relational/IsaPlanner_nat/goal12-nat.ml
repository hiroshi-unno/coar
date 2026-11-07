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

let rec drop n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = Z then Cons(x, xs)
    else drop (minus n (S Z)) xs

let rec map f l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) -> Cons(f x, map f xs)

let main f n xs =
  assert(drop n (map f xs) = map f (drop n xs))


[@@@types
  " map :: (t1: (tx: nat) -> {ty: int | ty = (f tx)}) -> (t2: list) -> {t3: list | map[0:2](t2, t3)}
 main :: (t1: (tx: nat) -> {ty: int | ty = (f tx)}) -> (n:nat) -> (xs:list) -> unit"]
