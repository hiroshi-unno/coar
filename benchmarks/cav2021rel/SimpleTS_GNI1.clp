(*
while ( * ) { x ++; }; return (high + x);

Copy 1 is scheduled demonically
Copy 2 is scheduled angelically
*)

Inv(0, b, b1 : bool, x1, high1, b2 : bool, x2, high2) :-
  FN_DB(x1, high1, x2, high2, b), b1, b2, x1 = x2.
Inv(d', b, b1' : bool, x1', high1, b2 : bool, x2, high2) :-
  Inv(d, b, b1 : bool, x1, high1, b2 : bool, x2, high2),
  SchTF(d, b, b1 : bool, x1, high1, b2 : bool, x2, high2),
  b1 and (b1' and x1' = x1 + 1 or !b1' and x1' = x1) or
  !b1 and !b1' and x1' = x1,
  (!b1 or !b2 or d' = d + 1).
Inv(d', b, b1 : bool, x1, high1, b21 : bool, x21, high2),
Inv(d', b, b1 : bool, x1, high1, b22 : bool, x22, high2) :-
  Inv(d, b, b1 : bool, x1, high1, b2 : bool, x2, high2),
  SchFT(d, b, b1 : bool, x1, high1, b2 : bool, x2, high2),
  b2 and b21 and x21 = x2 + 1 and !b22 and x22 = x2 or
  !b2 and !b21 and x21 = x2 and !b22 and x22 = x1,
  (!b1 or !b2 or d' = d - 1).
Inv(d, b, b1' : bool, x1', high1, b21 : bool, x21, high2),
Inv(d, b, b1' : bool, x1', high1, b22 : bool, x22, high2) :-
  Inv(d, b, b1 : bool, x1, high1, b2 : bool, x2, high2),
  SchTT(d, b, b1 : bool, x1, high1, b2 : bool, x2, high2),
  b1 and (b1' and x1' = x1 + 1 or !b1' and x1' = x1) or
  !b1 and !b1' and x1' = x1,
  b2 and b21 and x21 = x2 + 1 and !b22 and x22 = x2 or
  !b2 and !b21 and x21 = x2 and !b22 and x22 = x1.

b1 :-
  Inv(d, b, b1 : bool, x1, high1, b2 : bool, x2, high2),
  SchTF(d, b, b1 : bool, x1, high1, b2 : bool, x2, high2),
  b2.
b2 :-
  Inv(d, b, b1 : bool, x1, high1, b2 : bool, x2, high2),
  SchFT(d, b, b1 : bool, x1, high1, b2 : bool, x2, high2),
  b1.
SchTF(d, b, b1 : bool, x1, high1, b2 : bool, x2, high2),
SchFT(d, b, b1 : bool, x1, high1, b2 : bool, x2, high2),
SchTT(d, b, b1 : bool, x1, high1, b2 : bool, x2, high2) :-
  Inv(d, b, b1 : bool, x1, high1, b2 : bool, x2, high2), b1 or b2.
-b <= d and d <= b and b >= 0 :-
  Inv(d, b, b1 : bool, x1, high1, b2 : bool, x2, high2), b1, b2.

high1 + x1 = high2 + x2 :-
  Inv(d, b, b1 : bool, x1, high1, b2 : bool, x2, high2), !b1, !b2.

WF_R2(b2 : bool, x2, high2, b21 : bool, x21, high2),
WF_R2(b2 : bool, x2, high2, b22 : bool, x22, high2) :-
  Inv(d, b, b1 : bool, x1, high1, b2 : bool, x2, high2),
  !b1, b2 and b21 and x21 = x2 + 1 and !b22 and x22 = x2.
