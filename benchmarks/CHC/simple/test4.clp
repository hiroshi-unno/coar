Inv(0,0).
Inv(i+1,j+1) :- Inv(i,j), i <= 999.
?- j > 1000, Inv(i,j).
