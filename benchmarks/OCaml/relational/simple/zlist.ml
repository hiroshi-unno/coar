type zlist = ZNil | ZCons of (int * int) * zlist

let rec zid l =
  match l with
  | ZNil -> ZNil
  | ZCons(x, xs) -> ZCons(x, xs)

let main x =
  let l = ZCons(x,ZNil) in
  assert(zid l = l)
 
