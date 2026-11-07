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

let rec zip l1 l2 =
  match (l1, l2) with
  | Nil, xs -> ZNil
  | xs, Nil -> ZNil
  | Cons(x, xs), Cons(y, ys) ->
    ZCons((x, y), zip xs ys)

let main xs ys =
  if xs = Nil then assert(zip Nil ys = ZNil)
  else ()
