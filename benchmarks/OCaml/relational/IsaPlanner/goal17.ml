let leq x y = x <= y

let main n =
  if n >= 0 then
    assert(leq n 0 = (n = 0))
  else ()
