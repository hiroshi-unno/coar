I(x,r) :- x >= 0, r = x.
I(x,r) :- x < 0, r = -x.
I(x',r') :- I(x,r), x > 0, x' = x - 1, r' = r - 1.
I(x',r') :- I(x,r), x <> 0, x <= 0, x' = x + 1, r' = r - 1.
r >= 0 :- I(x,r).

