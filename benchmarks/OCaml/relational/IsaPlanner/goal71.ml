type list = Nil | Cons of int * list

let leq x y = x <= y

let succ x = 1 + x

let main m n =
  if leq m n then
    assert(leq m (succ n))
  else ()
