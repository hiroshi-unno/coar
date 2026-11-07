let rec sum n =
  if n < 0 then n + sum (n + 1)
  else if n = 0 then 0
  else n + sum (n - 1)

let rec sum_down n m =
  if m = n then n
  else m + sum_down n (m - 1)

let main n =
  if n >= 0 then
    let s1 = sum n in
    let s2 = sum_down 0 n in
    assert(s1 = s2)
  else ()
