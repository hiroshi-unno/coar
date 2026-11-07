let rec flip_mod y x =
  if y < 0 then flip_mod (-y) x
  else if x < 0 then flip_mod y (x + y)
  else if x < y then x
  else flip_mod y (x - y)

let main x y =
  assert (flip_mod y x = flip_mod y (flip_mod y x))
