I(x,r) :- x >= -x, r = x + 10.
I(x,r) :- x < -x, r = -x + 10.
I(x',r') :- I(x,r), x <> -10, x <> 10, x < -10, x' = x + 1, r' = r - 1.
I(x',r') :- I(x,r), x <> -10, x <> 10, -10 <= x, x < 0, x' = x - 1, r' = r - 1.
I(x',r') :- I(x,r), x <> -10, x <> 10, 0 <= x, x < 10, x' = x + 1, r' = r - 1.
I(x',r') :- I(x,r), x <> -10, x <> 10, 10 <= x, x' = x - 1, r' = r - 1.
r >= 0 :- I(x,r).
