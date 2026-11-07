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


type tree = Node of nat * tree * tree | Leaf

let rec mirror t =
  match t with
  | Leaf -> Leaf
  | Node(x, y, z) -> Node(x, mirror z, mirror y)


let nmax x y =
  if less x y then y else x

let rec height t =
  match t with
  | Leaf -> Z
  | Node(x, y, z) ->
    plus (S Z) (nmax (height y) (height z))

let main a =
  assert(height (mirror a) = height a)

[@@@types
"height :: (t1: tree) -> {t2: nat | height[0:1](t1, t2) }"]

