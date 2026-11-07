let rec minus n m =
  if n <= m then 0
  else n - m

let main m n =
  if m >= 0 && n >= 0 then
    assert(minus (m + n) n = m)
  else ()
