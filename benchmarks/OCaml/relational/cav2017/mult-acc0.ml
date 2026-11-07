let rec mult x y =
  if y = 0 then 0
  else x + mult x (y - 1)

let rec mult_acc x y a =
  if y = 0 then a
  else mult_acc x (y - 1) (a + x)

let main x y a =
  let s1 = mult x y in
  let s2 = mult_acc x y 0 in
  assert(s1 = s2)

[@@@lemma "forall x y a r. mult_acc x y a = r => mult_acc x y (a - x) = r - x"]

