let rec mult x y =
  if y = 0 then 0
  else x + mult x (y - 1)

let main x y z  =
  let s1 = mult (x + y) z in
  let s2 = mult x z in
  let s3 = mult y z in
  assert(s1 = s2 + s3)
