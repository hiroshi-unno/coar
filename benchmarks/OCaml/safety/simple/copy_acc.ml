let rec copy x =
  if x = 0 then 0
  else 1 + copy (x - 1)

let rec copy_acc x a =
  if x = 0 then a
  else copy_acc (x - 1) (a + 1)

let main x =
  let s1 = copy x in
  let s2 = copy_acc x 0 in
  assert (s1 = s2)

[@@@assert "typeof(main) <: int -> unit"]
