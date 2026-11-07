let rec minus n m =
  if n <= m then 0
  else n - m

let main n m =
  if n >= 0 && m >= 0 then
    assert(minus (n + m) n = m)
  else ()
