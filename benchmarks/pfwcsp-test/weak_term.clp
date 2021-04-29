Inv(x) :- x <> 0.
Inv(x') :- Inv(x), x <> 0, FN_Angel(x,x').
WF_R(x,x') :- Inv(x), x <> 0, FN_Angel(x,x').