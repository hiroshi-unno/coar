(* 
f(int x) {
  while (x>0) { x = x - max( * , 1); }
}

g(int x) {
  while (x>0) { x = x - 1; } }
}

f and g co-terminate, angelically
f is scheduled angelically
g is scheduled demonically
*)

Inv(0, b, x1, x2) :- FN_DB(x1, x2, b), x1 = x2.
Inv(d', b, x1', x2) :- Inv(d, b, x1, x2), SchTF(d, b, x1, x2),
  x1 > 0 and FN_R(x1, nd) and (nd >= 1 and x1' = x1 - nd or x1' = x1 - 1) or
  x1 <= 0 and x1' = x1,
  (x1 <= 0 or x2 <= 0 or d' = d + 1).
Inv(d', b, x1, x2') :- Inv(d, b, x1, x2), SchFT(d, b, x1, x2),
  x2 > 0 and x2' = x2 - 1 or x2 <= 0 and x2' = x2,
  (x1 <= 0 or x2 <= 0 or d' = d - 1).
Inv(d, b, x1', x2') :- Inv(d, b, x1, x2), SchTT(d, b, x1, x2),
  x1 > 0 and FN_R(x1, nd) and (nd >= 1 and x1' = x1 - nd or x1' = x1 - 1) or
  x1 <= 0 and x1' = x1,
  x2 > 0 and x2' = x2 - 1 or x2 <= 0 and x2' = x2.

x1 > 0 :- Inv(d, b, x1, x2), SchTF(d, b, x1, x2), x2 > 0.
x2 > 0 :- Inv(d, b, x1, x2), SchFT(d, b, x1, x2), x1 > 0.
SchTF(d, b, x1, x2), SchFT(d, b, x1, x2), SchTT(d, b, x1, x2) :-
  Inv(d, b, x1, x2), x1 > 0 or x2 > 0.
-b <= d and d <= b and b >= 0 :- Inv(d, b, x1, x2), x1 > 0, x2 > 0.

WF_R1(x1, x1') :-
  Inv(d, b, x1, x2),
  x2 <= 0, x1 > 0 and FN_R(x1, nd) and (nd > 0 and x1' = x1 - nd or x1' = x1 - 1).
