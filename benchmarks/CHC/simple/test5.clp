Inv(0).
Inv(i+1) :- Inv(i), i<100.
?- Inv(i), i>100.
