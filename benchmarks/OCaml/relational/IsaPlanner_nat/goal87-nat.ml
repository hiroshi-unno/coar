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
type zlist = ZNil | ZCons of (nat * nat) * zlist

let rec append l ys =
  match l with
  | Nil -> ys
  | Cons(x, xs) ->
    Cons(x, append xs ys)

let rec zappend l ys =
  match l with
  | ZNil -> ys
  | ZCons(x, xs) ->
    ZCons(x, zappend xs ys)

let rec rev l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) -> append (rev xs) (Cons(x, Nil))

let rec zrev l =
  match l with
  | ZNil -> ZNil
  | ZCons(x, xs) -> zappend (zrev xs) (ZCons(x, ZNil))

let rec len l =
  match l with
  | Nil -> Z
  | Cons(x, xs) -> plus (S Z) (len xs)

let rec zip l1 l2 =
  match (l1, l2) with
  | Nil, xs -> ZNil
  | xs, Nil -> ZNil
  | Cons(x, xs), Cons(y, ys) ->
    ZCons((x, y), zip xs ys)

let main xs ys zs =
  if len xs = len ys then
    assert(zip (rev xs) (rev ys) = zrev (zip xs ys))
  else ()
