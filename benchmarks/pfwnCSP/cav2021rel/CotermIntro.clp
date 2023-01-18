(* 
f(int x, int y) {
  while (x>0) { x = x - y; }
}

g(int x, int y) {
  while (x>0) { x = x - 2 * y; }
}

f and g co-terminate
*)

Inv(0, b, x1, y1, x2, y2) :-
  FN_DB(x1, y1, x2, y2, b), x1 = x2, y1 = y2.
Inv(d', b, x1', y1, x2, y2) :-
  Inv(d, b, x1, y1, x2, y2), SchTF(d, b, x1, y1, x2, y2),
  x1 > 0 and x1' = x1 - y1 or x1 <= 0 and x1' = x1,
  (x1 <= 0 or x2 <= 0 or d' = d + 1).
Inv(d', b, x1, y1, x2', y2) :-
  Inv(d, b, x1, y1, x2, y2), SchFT(d, b, x1, y1, x2, y2),
  x2 > 0 and x2' = x2 - 2 * y2 or x2 <= 0 and x2' = x2,
  (x1 <= 0 or x2 <= 0 or d' = d - 1).
Inv(d, b, x1', y1, x2', y2) :-
  Inv(d, b, x1, y1, x2, y2), SchTT(d, b, x1, y1, x2, y2),
  x1 > 0 and x1' = x1 - y1 or x1 <= 0 and x1' = x1,
  x2 > 0 and x2' = x2 - 2 * y2 or x2 <= 0 and x2' = x2.

x1 > 0 :- Inv(d, b, x1, y1, x2, y2), SchTF(d, b, x1, y1, x2, y2), x2 > 0.
x2 > 0 :- Inv(d, b, x1, y1, x2, y2), SchFT(d, b, x1, y1, x2, y2), x1 > 0.
SchTF(d, b, x1, y1, x2, y2), SchFT(d, b, x1, y1, x2, y2), SchTT(d, b, x1, y1, x2, y2) :-
  Inv(d, b, x1, y1, x2, y2), x1 > 0 or x2 > 0.
-b <= d and d <= b and b >= 0:- Inv(d, b, x1, y1, x2, y2), x1 > 0, x2 > 0.

WF_R1(x1, y1, x1', y1) :-
  Inv(d, b, x1, y1, x2, y2),
  x2 <= 0, x1 > 0 and x1' = x1 - y1.
WF_R2(x2, y2, x2', y2) :-
  Inv(d, b, x1, y1, x2, y2),
  x1 <= 0, x2 > 0 and x2' = x2 - 2 * y2.
