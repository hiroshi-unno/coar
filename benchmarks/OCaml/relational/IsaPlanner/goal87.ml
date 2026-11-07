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
  | Nil -> 0
  | Cons(x, xs) -> 1 + len xs

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
