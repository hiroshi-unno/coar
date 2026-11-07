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

let rec takeWhile p l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if p x then Cons(x, takeWhile p xs)
    else Nil

let ftrue x = true

let main xs =
  assert(takeWhile ftrue xs = xs)

[@@@types
"takeWhile :: (t1: (x1: nat) -> {x2: bool | pred(x1,x2)}) -> (t2: list) -> {t3: list | takeWhile[0:2](t2, t3)}
"]
