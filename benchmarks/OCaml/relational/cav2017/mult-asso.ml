let rec mult x y =
  if y = 0 then 0
  else x + mult x (y - 1)

let main x y z =
  let s1 = mult (mult x y) z in
  let s2 = mult x (mult y z) in
  assert(s1 = s2)
