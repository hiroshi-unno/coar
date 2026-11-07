let less x y = x < y

let succ x = 1 + x

let main i m =
  if i >= 0 && m >= 0 then
    assert(less i (succ (i + m)))
  else ()
