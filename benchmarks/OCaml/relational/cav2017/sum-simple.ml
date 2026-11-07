let rec sum n =
  if n < 0 then n + sum (n + 1)
  else if n = 0 then 0
  else n + sum (n - 1)

let main n =
  if n > 0 then
    let s1 = sum n in
    let s2 = sum (n - 1) in
    assert(s1 = n + s2)
  else ()
