Inv(x) :- x <> 0.
Inv(x-1) :- Inv(x), x > 0.
Inv(x+1) :- Inv(x), x < 0.
WF_R(x,x-1) :- Inv(x), x > 0.
WF_R(x,x+1) :- Inv(x), x < 0.