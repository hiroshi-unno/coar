type list = Nil | Cons of int * list
type zlist = ZNil | ZCons of (int * int) * zlist

let rec take n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Nil
    else Cons(x, take (n - 1) xs)

let rec ztake n l =
  match l with
  | ZNil -> ZNil
  | ZCons(x, xs) ->
    if n = 0 then ZNil
    else ZCons(x, ztake (n - 1) xs)

let rec zip l1 l2 =
  match (l1, l2) with
  | Nil, xs -> ZNil
  | xs, Nil -> ZNil
  | Cons(x, xs), Cons(y, ys) ->
    ZCons((x, y), zip xs ys)

let main n xs ys =
  assert(ztake n (zip xs ys) = zip (take n xs) (take n ys))

