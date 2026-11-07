type list = Nil | Cons of int * list
type zlist = ZNil | ZCons of (int * int) * zlist

let rec zip l1 l2 =
  match (l1, l2) with
  | Nil, xs -> ZNil
  | xs, Nil -> ZNil
  | Cons(x, xs), Cons(y, ys) ->
    ZCons((x, y), zip xs ys)

let main xs ys =
  if xs = Nil then assert(zip Nil ys = ZNil)
  else ()
