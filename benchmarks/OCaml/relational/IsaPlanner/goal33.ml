let less (x: int) (y: int) = x < y

let leq (x: int) (y: int) = x <= y

let nmin x y =
  if less x y then x else y

let main a b =
  assert((nmin a b = a) = leq a b)
