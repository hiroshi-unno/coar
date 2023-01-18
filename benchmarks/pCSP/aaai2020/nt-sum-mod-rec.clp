(*
let rec sum x =
  if x > 0 then
    (if *E then x + sum (x-1) else sum x)
  else 0
let main x =
  assume (x >= 0); sum x; assert false
*)
P(x, x + y1), P(x, y2) :- x > 0, P(x - 1, y1), P(x, y2).
P(x, y) :- x <= 0, y = 0.
bot :- x >= 0, P(x, y).
