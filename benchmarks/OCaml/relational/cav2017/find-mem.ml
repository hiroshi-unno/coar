type list = Nil | Cons of int * list
type exc = Not_found

let eq x y = x = y

let rec mem x l =
  match l with
  | Nil -> false
  | Cons(y, ys) -> x = y || mem x ys

let rec find g(*ghost*) p l ok exc =
  match l with
  | Nil -> exc Not_found
  | Cons(x, xs) -> if p x then ok x else find g p xs ok exc

let kok l x y = assert(mem x l)
let kex l x Not_found = assert (not(mem x l))

let main l x =
  find x (eq x) l (kok l x) (kex l x)
