type list = Nil | Cons of int * list
type zlist = ZNil | ZCons of (int * int) * zlist

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

let rec len l =
  match l with
  | Nil -> 0
  | Cons(x, xs) -> 1 + len xs

let rec take n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Nil
    else Cons(x, take (n - 1) xs)

let rec drop n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Cons(x, xs)
    else drop (n - 1) xs

let rec zip l1 l2 =
  match (l1, l2) with
  | Nil, xs -> ZNil
  | xs, Nil -> ZNil
  | Cons(x, xs), Cons(y, ys) ->
    ZCons((x, y), zip xs ys)

let main xs ys zs =
  assert(zip (append xs ys) zs =
      zappend
	(zip xs (take (len xs) zs))
	(zip ys (drop (len xs) zs)))

[@@@types
"len :: (t1: list) -> {t2: int | len[0:1](t1, t2) && t2 >= 0}
"]
