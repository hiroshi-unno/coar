type list = Nil | Cons of int * list
type zlist = ZNil | ZCons of (int * int) * zlist

let rec drop n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Cons(x, xs)
    else drop (n - 1) xs

let rec zdrop n l =
  match l with
  | ZNil -> ZNil
  | ZCons(x, xs) ->
    if n = 0 then ZCons(x, xs)
    else zdrop (n - 1) xs

let rec zip l1 l2 =
  match (l1, l2) with
  | Nil, xs -> ZNil
  | xs, Nil -> ZNil
  | Cons(x, xs), Cons(y, ys) ->
    ZCons((x, y), zip xs ys)

let main n xs ys =
  if n >= 0 then
    assert(zdrop n (zip xs ys) = zip (drop n xs) (drop n ys))
  else ()
