type list = Nil | Cons of int * list
type llist = LNil | LCons of list * llist

let rec map_cons x l =
  match l with
  | LNil -> LNil
  | LCons (xs, ls) -> LCons( Cons(x, xs), map_cons x ls)

let rec prefixes x =
  match x with
  | Nil -> LNil
  | Cons(u, us) ->
    let res = prefixes us in
    LCons( Cons(u, Nil), map_cons u res)

let rec sum x =
  match x with
  | Nil -> 0
  | Cons (u, us) -> u + sum us

let rec map_sum l =
  match l with
  | LNil -> Nil
  | LCons (u, us) -> Cons(sum u, map_sum us)

let rec sps acc l =
  match l with
  | Nil -> 0
  | Cons(u, us) -> acc + u + sps (acc + u) us

let rec len l =
  match l with
  | Nil -> 0
  | Cons(u, us) -> 1 + len us

let main a x =
  assert (sps a x = sum (map_sum (prefixes x)) + a * len x)


