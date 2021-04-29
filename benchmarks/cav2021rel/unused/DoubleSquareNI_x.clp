(* 
pre(x1 == x2)
doubleSquare(bool h, int x){
  int z, y=0;
  if(h) { z = 2*x; }
  else { z = x; }
  while (z>0) {
    z--;
    y = y+x;
  }
  if(!h) { y = 2*y; }
  return y;
}
post(y1 == y2)
*)

(* specialized with x1 = x2 *)

Inv(x, y1, z1, h1 : bool, y2, z2, h2 : bool) :-
  y1 = 0, (h1 and z1 = 2 * x or !h1 and z1 = x),
  y2 = 0, (h2 and z2 = 2 * x or !h2 and z2 = x).
Inv(x, y1', z1', h1 : bool, y2, z2, h2 : bool) :-
  Inv(x, y1, z1, h1 : bool, y2, z2, h2 : bool),
  SchTF(x, y1, z1, h1 : bool, y2, z2, h2 : bool),
  z1 > 0 and z1' = z1 - 1 and y1' = y1 + x or z1 <= 0 and z1' = z1 and y1' = y1.
Inv(x, y1, z1, h1 : bool, y2', z2', h2 : bool) :-
  Inv(x, y1, z1, h1 : bool, y2, z2, h2 : bool),
  SchFT(x, y1, z1, h1 : bool, y2, z2, h2 : bool),
  z2 > 0 and z2' = z2 - 1 and y2' = y2 + x or z2 <= 0 and z2' = z2 and y2' = y2.
Inv(x, y1', z1', h1 : bool, y2', z2', h2 : bool) :-
  Inv(x, y1, z1, h1 : bool, y2, z2, h2 : bool),
  SchTT(x, y1, z1, h1 : bool, y2, z2, h2 : bool),
  z1 > 0 and z1' = z1 - 1 and y1' = y1 + x or z1 <= 0 and z1' = z1 and y1' = y1,
  z2 > 0 and z2' = z2 - 1 and y2' = y2 + x or z2 <= 0 and z2' = z2 and y2' = y2.

z1 > 0 :-
  Inv(x, y1, z1, h1 : bool, y2, z2, h2 : bool),
  SchTF(x, y1, z1, h1 : bool, y2, z2, h2 : bool), z2 > 0.
z2 > 0 :-
  Inv(x, y1, z1, h1 : bool, y2, z2, h2 : bool),
  SchFT(x, y1, z1, h1 : bool, y2, z2, h2 : bool), z1 > 0.
SchTF(x, y1, z1, h1 : bool, y2, z2, h2 : bool), SchFT(x, y1, z1, h1 : bool, y2, z2, h2 : bool), SchTT(x, y1, z1, h1 : bool, y2, z2, h2 : bool) :-
  Inv(x, y1, z1, h1 : bool, y2, z2, h2 : bool),
  z1 > 0 or z2 > 0.

y1' = y2' :-
  Inv(x, y1, z1, h1 : bool, y2, z2, h2 : bool),
  z1 <= 0, z2 <= 0,
  h1 and y1' = y1 or !h1 and y1' = 2 * y1,
  h2 and y2' = y2 or !h2 and y2' = 2 * y2.
