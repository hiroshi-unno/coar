let less (x: int) (y: int) = x < y

let nmin x y =
  if less x y then x else y

let main a b c =
  assert(nmin (nmin a b) c = nmin a (nmin b c))
