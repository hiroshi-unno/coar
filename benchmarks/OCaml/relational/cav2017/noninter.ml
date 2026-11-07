let rec noninter h l1 l2 l3 =
  if l1 = 0 then l2 + l3
  else noninter h (l1 - 1) (l3 + h) (l2 - h)

let main h1 h2 l1 l2 l3 =
  assert(noninter h1 l1 l2 l3 = noninter h2 l1 l2 l3)
