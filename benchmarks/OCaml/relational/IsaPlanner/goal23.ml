let less (x: int) (y: int) = x < y

let nmax x y =
  if less x y then y else x

let main a b =
  assert(nmax a b = nmax b a)
