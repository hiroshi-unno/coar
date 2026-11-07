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

let rec takeWhile f l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if f x then Cons(x, takeWhile f xs)
    else Nil

let rec dropWhile f l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if f x then dropWhile f xs
    else Cons(x, xs)

let rec append l ys =
  match l with
  | Nil -> ys
  | Cons(x, xs) ->
    Cons(x, append xs ys)

let main f xs =
  assert(append (takeWhile f xs) (dropWhile f xs) = xs)

[@@@types
"takeWhile :: (t1: (tx: nat) -> {ty: bool | ty = (f tx)}) -> (t2: list) -> {t3: list | takeWhile[0:2](t2, t3)}
 dropWhile :: (t1: (tx: nat) -> {ty: bool | ty = (f tx)}) -> (t2: list) -> {t3: list | dropWhile[0:2](t2, t3)}
 main :: (t1: (tx: nat) -> {ty: bool | ty = (f tx)}) -> (xs:list) -> unit"]
