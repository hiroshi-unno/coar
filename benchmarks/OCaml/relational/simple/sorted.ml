type list = Nil | Cons of int * list

let rec insert x l =
  match l with
  | Nil -> Cons(x,Nil)
  | Cons(y,l) -> 
     if x <= y then Cons(x,Cons(y,l)) else Cons(y,insert x l)

let rec sorted l =
  match l with
  | Nil -> true
  | Cons(x,Nil) -> true
  | Cons(x1,Cons(x2,xs)) -> x1<=x2 && sorted (Cons(x2,xs))

let main x l =
  if sorted l then
    assert(sorted (insert x l))
