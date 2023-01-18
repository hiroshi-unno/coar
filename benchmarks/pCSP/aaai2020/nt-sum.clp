(*
assume (x > 0 /\ y = 0);
(while x > 0 do
  if *E then y := y + x; x := x - 1);
assert false
*)
I(x, y) :- x > 0, y = 0.
I(x, y), I(x - 1, y + x) :- I(x, y), x > 0.
bot :- I(x, y), x <= 0.
