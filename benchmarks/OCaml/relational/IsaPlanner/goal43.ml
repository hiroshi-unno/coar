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
"takeWhile :: (t1: (tx: int) -> {ty: bool | ty = (f tx)}) -> (t2: list) -> {t3: list | takeWhile[0:2](t2, t3)}
 dropWhile :: (t1: (tx: int) -> {ty: bool | ty = (f tx)}) -> (t2: list) -> {t3: list | dropWhile[0:2](t2, t3)}
 main :: (t1: (tx: int) -> {ty: bool | ty = (f tx)}) -> (xs:list) -> unit"]
