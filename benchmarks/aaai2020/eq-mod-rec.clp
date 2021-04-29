(* 
let rec loop x y =
  if x > 0 then
    if *E then loop (x - 1) y
    else loop (x - 1) (y + 1)
  else y
let main x =
  let z = loop x 0 in assert (z = x)
*)
P(x, y, z1), P(x, y, z2) :- x > 0, P(x - 1, y, z1), P(x - 1, y + 1, z2).
P(x, y, z) :- x <= 0, z = y.
z = x :- P(x, 0, z).
