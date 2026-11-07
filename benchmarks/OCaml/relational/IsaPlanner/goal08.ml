let rec minus n m =
  if n <= m then 0
  else n - m

let main k n m =
  if k >= 0 && n >= 0 && m >= 0 then
    assert(minus (k + m) (k + n) = minus m n)
  else ()
