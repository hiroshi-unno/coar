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

let rec take n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = Z then Nil
    else Cons(x, take (minus n (S Z)) xs)

let main n xs =
  assert(append (take n xs) (drop n xs) = xs)

(*
[@@@types
"append :: (t1: list) -> (t2: list) -> {t3: list | append(t1, t2, t3)}
 drop :: (t1: int) -> (t2: list) -> {t3: list | drop(t1, t2, t3)}
 take :: (t1: int) -> (t2: list) -> {t3: list | take(t1, t2, t3)}"]
 *)
