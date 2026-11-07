type list = Nil | Cons of int * list

let rec len l =
  match l with
  | Nil -> 0
  | Cons(x, xs) -> 1 + len xs

let rec delete x l =
  match l with
  | Nil -> Nil
  | Cons(y, ys) ->
    if x = y then delete x ys
    else Cons(y, delete x ys)

let leq x y = x <= y

let main l x =
  assert(leq (len (delete x l)) (len l))
