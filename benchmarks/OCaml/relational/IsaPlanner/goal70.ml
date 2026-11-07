type list = Nil | Cons of int * list

let leq x y = x <= y

let main m n =
  if m >= 0 && n >= 0 then
    assert(leq n (m + n))
  else ()
