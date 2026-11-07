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

let succ x = plus (S Z) x

let main n x xs =
  assert(drop (succ n) (Cons(x, xs)) = drop n xs)

(* Require 1 min 30 sec AND this option *)
(* [@@@option "-extract-entailment -induct-limit=2"] *)
