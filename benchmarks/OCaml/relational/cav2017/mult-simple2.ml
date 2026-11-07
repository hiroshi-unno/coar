let rec mult x y =
  if y = 0 then 0
  else x + mult x (y - 1)

let main x y =
  if y >= 0 then
    let s1 = mult x y in
    let s2 = mult x (y + 1) in
    assert(s1 + x = s2)
  else ()
