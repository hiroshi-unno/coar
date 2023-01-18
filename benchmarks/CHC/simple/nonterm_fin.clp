Inv(x) :- x > 0.
Inv(x-1), Inv(x+1) :- Inv(x), x <> 0.
bot :- Inv(x), x = 0.