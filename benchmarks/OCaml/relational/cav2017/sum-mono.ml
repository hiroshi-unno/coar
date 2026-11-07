let rec sum n =
  if n < 0 then n + sum (n + 1)
  else if n = 0 then 0
  else n + sum (n - 1)

let main n1 n2 =
  if n1 <= n2 then
    let s1 = sum n1 in
    let s2 = sum n2 in
    assert(s1 <= s2)
  else ()
