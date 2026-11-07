let rec mult x y =
  if y = 0 then 0
  else x + mult x (y - 1)

let apply2 f x y = f x y

let main n m =
  let s1 = apply2 mult n m in
  let s2 = mult n m in
  assert(s2 = s1)
