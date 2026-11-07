let rec sum n =
  if n < 0 then n + sum (n + 1)
  else if n = 0 then 0
  else n + sum (n - 1)

let rec sum_up n m =
  if n = m then n
  else n + sum_up (n + 1) m

let main n =
  if n < 0 then
    let s1 = sum n in
    let s2 = sum_up n 0 in
    assert(s1 = s2)
  else ()
