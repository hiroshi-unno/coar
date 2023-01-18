Inv(x) :- x > 0.
Inv(r-x) :- Inv(x), x > 0, FN_Angel(x,r).
bot :- Inv(x), x <= 0.