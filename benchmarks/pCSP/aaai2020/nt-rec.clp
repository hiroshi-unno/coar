(*
let rec loop x =
  if x >= 0 then
    (if *E then loop (x-1) else loop (x+1))
  else x
let main x =
  assume (x >= 0); loop x; assert false
*)
P(x,y) :- x < 0, x = y.
P(x, y1), P(x, y2) :- x >= 0, P(x-1, y1), P(x+1, y2).
bot :- x >= 0, P(x, y).
