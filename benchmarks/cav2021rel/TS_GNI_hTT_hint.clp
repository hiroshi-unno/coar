(*
if (high) {
  x = *; // needs to depend on the return value of the other copy
  if (x >= low) { return x; } else { while (1) { } }
} else {
  x = low;
  while ( * ) { x++; }
  return x;
}

Copy 1 is scheduled demonically
Copy 2 is scheduled angelically

specialized with high1 and high2
*)

Inv(pr (* prophecy variable for the return value of Copy 1 *),
    0, b, b1 : bool, x1, low1, b2 : bool, x2, low2) :-
  FN_DB(x1, low1, x2, low2, b),
  b1, b2, low1 = low2,
  x1 = nd1,
  FN_R(pr, low2, x2).
Inv(pr, d', b, b1' : bool, x1', low1, b2 : bool, x2, low2) :-
  Inv(pr, d, b, b1 : bool, x1, low1, b2 : bool, x2, low2),
  SchTF(pr, d, b, b1 : bool, x1, low1, b2 : bool, x2, low2),
  b1 and (x1 >= low1 and !b1' and x1' = x1 or
          x1 < low1 and b1' and x1' = x1) or
  !b1 and !b1' and x1' = x1,
  (!b1 and pr = x1 or !b2 or d' = d + 1).
Inv(pr, d', b, b1 : bool, x1, low1, b2' : bool, x2', low2) :-
  Inv(pr, d, b, b1 : bool, x1, low1, b2 : bool, x2, low2),
  SchFT(pr, d, b, b1 : bool, x1, low1, b2 : bool, x2, low2),
  b2 and (x2 >= low2 and !b2' and x2' = x2 or
          x2 < low2 and b2' and x2' = x2) or
  !b2 and !b2' and x2' = x2,
  (!b1 and pr = x1 or !b2 or d' = d - 1).
Inv(pr, d, b, b1' : bool, x1', low1, b2' : bool, x2', low2) :-
  Inv(pr, d, b, b1 : bool, x1, low1, b2 : bool, x2, low2),
  SchTT(pr, d, b, b1 : bool, x1, low1, b2 : bool, x2, low2),
  b1 and (x1 >= low1 and !b1' and x1' = x1 or
          x1 < low1 and b1' and x1' = x1) or
  !b1 and !b1' and x1' = x1,
  b2 and (x2 >= low2 and !b2' and x2' = x2 or
          x2 < low2 and b2' and x2' = x2) or
  !b2 and !b2' and x2' = x2.

b1 or pr <> x1 :-
  Inv(pr, d, b, b1 : bool, x1, low1, b2 : bool, x2, low2),
  SchTF(pr, d, b, b1 : bool, x1, low1, b2 : bool, x2, low2),
  b2.
b2 :-
  Inv(pr, d, b, b1 : bool, x1, low1, b2 : bool, x2, low2),
  SchFT(pr, d, b, b1 : bool, x1, low1, b2 : bool, x2, low2),
  b1 or pr <> x1.
SchTF(pr, d, b, b1 : bool, x1, low1, b2 : bool, x2, low2),
SchFT(pr, d, b, b1 : bool, x1, low1, b2 : bool, x2, low2),
SchTT(pr, d, b, b1 : bool, x1, low1, b2 : bool, x2, low2) :-
  Inv(pr, d, b, b1 : bool, x1, low1, b2 : bool, x2, low2), b1 or pr <> x1 or b2.
-b <= d and d <= b and b >= 0 :-
  Inv(pr, d, b, b1 : bool, x1, low1, b2 : bool, x2, low2), b1 or pr <> x1, b2.

x1 = x2 :-
  Inv(pr, d, b, b1 : bool, x1, low1, b2 : bool, x2, low2),
  !b1 and pr = x1 (* if the prophecy is correct *), !b2.

WF_R2(x2, low2, x2', low2) :-
  Inv(pr, d, b, b1 : bool, x1, low1, b2 : bool, x2, low2),
  !b1 and pr = x1 (* if the prophecy is correct *),
  b2 and x2 < low2 and x2' = x2.

(* hint for non-relational invariant *)
b1 or x1 >= low1 :- Inv(pr, d, b, b1 : bool, x1, low1, b2 : bool, x2, low2).
