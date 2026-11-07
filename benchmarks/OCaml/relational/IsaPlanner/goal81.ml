let rec minus n m =
  if n <= m then 0
  else n - m

let succ x = 1 + x

let main m n k =
  if m >= 0 && n >= 0 && k >= 0 then
    assert(minus (minus (succ m) n) (succ k) = minus (minus m n) k)
  else ()
