(* 
if (high) {
  while (x>0) { x = x - max( * , 1); }
} else {
  while (x>0) { x = x - 1; }
}

Copy 1 is scheduled angelically
Copy 2 is scheduled demonically
*)

Inv(0, b, high1 : bool, x1, high2 : bool, x2) :- FN_DB(high1 : bool, x1, high2 : bool, x2, b), x1 = x2.
Inv(d', b, high1 : bool, x1', high2 : bool, x2) :-
  Inv(d, b, high1 : bool, x1, high2 : bool, x2), SchTF(d, b, high1 : bool, x1, high2 : bool, x2),
  high1 and x1 > 0 and FN_R(high1 : bool, x1, nd) and (nd >= 1 and x1' = x1 - nd or x1' = x1 - 1) and d' = d + 1 or
  !high1 and x1 > 0 and x1' = x1 - 1 or
  x1 <= 0 and x1' = x1,
  (x1 <= 0 or x2 <= 0 or d' = d + 1).
Inv(d', b, high1 : bool, x1, high2 : bool, x2') :-
  Inv(d, b, high1 : bool, x1, high2 : bool, x2), SchFT(d, b, high1 : bool, x1, high2 : bool, x2),
  high2 and x2 > 0 and nd >= 1 and x2' = x2 - nd or
  !high2 and x2 > 0 and x2' = x2 - 1 or
  x2 <= 0 and x2' = x2,
  (x1 <= 0 or x2 <= 0 or d' = d - 1).
Inv(d, b, high1 : bool, x1', high2 : bool, x2') :-
  Inv(d, b, high1 : bool, x1, high2 : bool, x2), SchTT(d, b, high1 : bool, x1, high2 : bool, x2),
  high1 and x1 > 0 and FN_R(high1 : bool, x1, nd) and (nd >= 1 and x1' = x1 - nd or x1' = x1 - 1) or
  !high1 and x1 > 0 and x1' = x1 - 1 or
  x1 <= 0 and x1' = x1,
  high2 and x2 > 0 and nd >= 1 and x2' = x2 - nd or
  !high2 and x2 > 0 and x2' = x2 - 1 or
  x2 <= 0 and x2' = x2.

x1 > 0 :-
  Inv(d, b, high1 : bool, x1, high2 : bool, x2), SchTF(d, b, high1 : bool, x1, high2 : bool, x2),
  x2 > 0.
x2 > 0 :-
  Inv(d, b, high1 : bool, x1, high2 : bool, x2), SchFT(d, b, high1 : bool, x1, high2 : bool, x2),
  x1 > 0.
SchTF(d, b, high1 : bool, x1, high2 : bool, x2),
SchFT(d, b, high1 : bool, x1, high2 : bool, x2),
SchTT(d, b, high1 : bool, x1, high2 : bool, x2) :-
  Inv(d, b, high1 : bool, x1, high2 : bool, x2), x1 > 0 or x2 > 0.
-b <= d and d <= b and b >= 0 :-
  Inv(d, b, high1 : bool, x1, high2 : bool, x2), x1 > 0, x2 > 0.

top :- Inv(d, b, high1 : bool, x1, high2 : bool, x2), x1 <= 0, x2 <= 0.

WF_R1(high1 : bool, x1, high1 : bool, x1') :-
  Inv(d, b, high1 : bool, x1, high2 : bool, x2),
  x2 <= 0, 
  high1 and x1 > 0 and FN_R(high1 : bool, x1, nd) and (nd >= 1 and x1' = x1 - nd or x1' = x1 - 1) or
  !high1 and x1 > 0 and x1' = x1 - 1.
