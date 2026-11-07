let rec sum_down n m =
  if m = n then n
  else m + sum_down n (m - 1)

let rec sum_up n m =
  if n = m then n
  else n + sum_up (n + 1) m

let main x y =
  assert(sum_down x y = sum_up x y)
