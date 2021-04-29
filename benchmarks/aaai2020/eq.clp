(* 
assume (x = x0 /\ y = 0}
(while x != 0 do
  x := x - 1; if *E then y := y + 1);
assert (y = x0)
*)
I(x0, x, y) :- x = x0, y = 0.
I(x0, x - 1, y + 1), I(x0, x - 1, y) :- I(x0, x, y), x \= 0.
y = x0 :- I(x0, x, y), x = 0.
