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

let rec take n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = Z then Nil
    else Cons(x, take (minus n (S Z)) xs)

let rec map f l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    let a = f x in
    Cons(x, map f xs)

let main f n xs =
  assert(take n (map f xs) = map f (take n xs))

[@@@types
"map :: (t1: (tx: nat) -> {ty: nat | ty = (f tx)}) -> (t2: list) -> {t3: list | map[0:2](t2, t3)}
 main :: (t1: (tx: nat) -> {ty: nat | ty = (f tx)}) -> (n:nat) -> (xs:list) -> unit"]
