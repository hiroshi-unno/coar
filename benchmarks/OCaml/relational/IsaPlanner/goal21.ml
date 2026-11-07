let leq x y = x <= y

let main n m =
  if n >= 0 && m >= 0 then
    assert(leq n (n + m))
  else ()
