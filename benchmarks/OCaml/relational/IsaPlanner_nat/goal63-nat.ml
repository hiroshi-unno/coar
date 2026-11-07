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

let rec last l =
  match l with
  | Nil -> Z
  | Cons(x, xs) ->
    if xs = Nil then x
    else last xs

let main x xs =
  if xs <> Nil then
    assert(last (Cons(x, xs)) = last xs)
  else ()
