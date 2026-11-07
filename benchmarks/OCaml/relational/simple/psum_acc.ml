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

let rec psum_acc acc l =
  match l with
  | Nil -> Nil
  | Cons(u, us) -> Cons(u + acc, psum_acc (acc + u) us)

let main x =
  assert (psum_acc 0 x = map_sum (prefixes x))


