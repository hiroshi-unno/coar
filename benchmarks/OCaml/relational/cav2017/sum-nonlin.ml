let rec sum n =
  if n < 0 then n + sum (n + 1)
  else if n = 0 then 0
  else n + sum (n - 1)

let main n =
  if n >= 0 then assert (2 * sum n = n * (n + 1))
