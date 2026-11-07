let rec minus n m =
  if n <= m then 0
  else n - m

let main m =
  if m >= 0 then
    assert(minus m m = 0)
  else ()
