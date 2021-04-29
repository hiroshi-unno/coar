(* 
pre(low1 == low2)
halfSquare(int h, int low){
  assume(low > h > 0);
  int i = 0, y = 0, v = 0;
  while (h > i) {
    i++; y += y;
  }
  v = 1;
  while (low > i) {
    i++; y += y;
  }
  return y;
}
post(y1 == y2)
*)

Inv(b1 : bool, h1, low1, i1, y1, v1, b2 : bool, h2, low2, i2, y2, v2) :-
  low1 = low2, low1 > h1, h1 > 0, low2 > h2, h2 > 0,
  b1, i1 = 0, y1 = 0, v1 = 0,
  b2, i2 = 0, y2 = 0, v2 = 0.

Inv(b1' : bool, h1, low1, i1', y1', v1', b2 : bool, h2, low2, i2, y2, v2) :-
  Inv(b1 : bool, h1, low1, i1, y1, v1, b2 : bool, h2, low2, i2, y2, v2),
  SchTF(b1 : bool, h1, low1, i1, y1, v1, b2 : bool, h2, low2, i2, y2, v2),
  b1 and h1 > i1 and b1' and i1' = i1 + 1 and y1' = y1 + y1 and v1' = v1 or
  b1 and h1 <= i1 and !b1' and i1' = i1 and y1' = y1 and v1' = 1 or
  !b1 and low1 > i1 and !b1' and i1' = i1 + 1 and y1' = y1 + y1 and v1' = v1 or
  !b1 and low1 <= i1 and !b1' and i1' = i1 and y1' = y1 and v1' = v1.
Inv(b1 : bool, h1, low1, i1, y1, v1, b2' : bool, h2, low2, i2', y2', v2') :-
  Inv(b1 : bool, h1, low1, i1, y1, v1, b2 : bool, h2, low2, i2, y2, v2),
  SchFT(b1 : bool, h1, low1, i1, y1, v1, b2 : bool, h2, low2, i2, y2, v2),
  b2 and h2 > i2 and b2' and i2' = i2 + 1 and y2' = y2 + y2 and v2' = v2 or
  b2 and h2 <= i2 and !b2' and i2' = i2 and y2' = y2 and v2' = 1 or
  !b2 and low2 > i2 and !b2' and i2' = i2 + 1 and y2' = y2 + y2 and v2' = v2 or
  !b2 and low2 <= i2 and !b2' and i2' = i2 and y2' = y2 and v2' = v2.
Inv(b1' : bool, h1, low1, i1', y1', v1', b2' : bool, h2, low2, i2', y2', v2') :-
  Inv(b1 : bool, h1, low1, i1, y1, v1, b2 : bool, h2, low2, i2, y2, v2),
  SchTT(b1 : bool, h1, low1, i1, y1, v1, b2 : bool, h2, low2, i2, y2, v2),
  b1 and h1 > i1 and b1' and i1' = i1 + 1 and y1' = y1 + y1 and v1' = v1 or
  b1 and h1 <= i1 and !b1' and i1' = i1 and y1' = y1 and v1' = 1 or
  !b1 and low1 > i1 and !b1' and i1' = i1 + 1 and y1' = y1 + y1 and v1' = v1 or
  !b1 and low1 <= i1 and !b1' and i1' = i1 and y1' = y1 and v1' = v1,
  b2 and h2 > i2 and b2' and i2' = i2 + 1 and y2' = y2 + y2 and v2' = v2 or
  b2 and h2 <= i2 and !b2' and i2' = i2 and y2' = y2 and v2' = 1 or
  !b2 and low2 > i2 and !b2' and i2' = i2 + 1 and y2' = y2 + y2 and v2' = v2 or
  !b2 and low2 <= i2 and !b2' and i2' = i2 and y2' = y2 and v2' = v2.

b1 or low1 > i1 :-
  Inv(b1 : bool, h1, low1, i1, y1, v1, b2 : bool, h2, low2, i2, y2, v2),
  SchTF(b1 : bool, h1, low1, i1, y1, v1, b2 : bool, h2, low2, i2, y2, v2),
  b2 or low2 > i2.
b2 or low2 > i2 :-
  Inv(b1 : bool, h1, low1, i1, y1, v1, b2 : bool, h2, low2, i2, y2, v2),
  SchFT(b1 : bool, h1, low1, i1, y1, v1, b2 : bool, h2, low2, i2, y2, v2),
  b1 or low1 > i1.
SchTF(b1 : bool, h1, low1, i1, y1, v1, b2 : bool, h2, low2, i2, y2, v2),
SchFT(b1 : bool, h1, low1, i1, y1, v1, b2 : bool, h2, low2, i2, y2, v2),
SchTT(b1 : bool, h1, low1, i1, y1, v1, b2 : bool, h2, low2, i2, y2, v2) :-
  Inv(b1 : bool, h1, low1, i1, y1, v1, b2 : bool, h2, low2, i2, y2, v2),
  b1 or low1 > i1 or b2 or low2 > i2.

y1 = y2 :-
  Inv(b1 : bool, h1, low1, i1, y1, v1, b2 : bool, h2, low2, i2, y2, v2),
  !b1, low1 <= i1, !b2, low2 <= i2.
