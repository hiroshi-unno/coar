(*
assume (x >= 0);
while (x >= 0) do
  if *E then x := x - 1 else x := x + 1;
assert false
*)
I(x) :- x >= 0.
I(x - 1), I(x + 1) :- I(x), x >= 0.
bot :- I(x), x < 0.
