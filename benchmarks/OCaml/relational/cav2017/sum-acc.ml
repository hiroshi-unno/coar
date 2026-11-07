let rec sum n =
  if n < 0 then n + sum (n + 1)
  else if n = 0 then 0
  else n + sum (n - 1)

let rec sum_acc n a =
  if n < 0 then sum_acc (n + 1) (a + n)
  else if n = 0 then a
  else sum_acc (n - 1) (a + n)

let main n a =
  let s1 = sum n in
  let s2 = sum_acc n a in
  assert(s1 + a = s2)
