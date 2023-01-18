P(x,r) :- x<=0, r=0.
P(x,r) :- P(x-1,y), x>0, r=x+y.
?- P(x,r), r<=x.
