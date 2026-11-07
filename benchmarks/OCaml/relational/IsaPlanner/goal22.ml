let less (x: int) (y: int) = x < y

let nmax x y =
  if less x y then y else x

let main a b c =
  assert(nmax (nmax a b) c = nmax a (nmax b c))
