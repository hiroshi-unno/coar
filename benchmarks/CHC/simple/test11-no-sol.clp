Inv(0,0).
Inv(i,j) :- Inv(i-1,j-1).
?- Inv(i,j), i = j.
