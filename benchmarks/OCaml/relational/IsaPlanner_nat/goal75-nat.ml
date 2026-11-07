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

let rec append l ys =
  match l with
  | Nil -> ys
  | Cons(x, xs) ->
    Cons(x, append xs ys)

let rec rev l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) -> append (rev xs) (Cons(x, Nil))

let rec filter f l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if f x then Cons(x, filter f xs)
    else filter f xs

let main p xs =
  assert(rev (filter p xs) = filter p (rev xs))
