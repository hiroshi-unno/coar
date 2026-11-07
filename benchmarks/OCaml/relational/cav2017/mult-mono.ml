let rec mult x y =
  if y <= 0 then 0
  else x + mult x (y - 1)

let main x1 y1 x2 y2 =
  if x1 <= x2 && y1 <= y2 && x1 >= 0 && y1 >= 0 then
    let s1 = mult x1 y1 in
    let s2 = mult x2 y2 in
    assert(s1 <= s2)
  else ()
