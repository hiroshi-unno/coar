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

(* specialized with !h1 and !h2 *)

Inv(x1, y1, z1, x2, y2, z2) :-
  x1 = x2,
  y1 = 0, z1 = x,
  y2 = 0, z2 = x.
Inv(x1, y1', z1', x2, y2, z2) :-
  Inv(x1, y1, z1, x2, y2, z2),
  SchTF(x1, y1, z1, x2, y2, z2),
  z1 > 0 and z1' = z1 - 1 and y1' = y1 + x1 or z1 <= 0 and z1' = z1 and y1' = y1.
Inv(x1, y1, z1, x2, y2', z2') :-
  Inv(x1, y1, z1, x2, y2, z2),
  SchFT(x1, y1, z1, x2, y2, z2),
  z2 > 0 and z2' = z2 - 1 and y2' = y2 + x2 or z2 <= 0 and z2' = z2 and y2' = y2.
Inv(x1, y1', z1', x2, y2', z2') :-
  Inv(x1, y1, z1, x2, y2, z2),
  SchTT(x1, y1, z1, x2, y2, z2),
  z1 > 0 and z1' = z1 - 1 and y1' = y1 + x1 or z1 <= 0 and z1' = z1 and y1' = y1,
  z2 > 0 and z2' = z2 - 1 and y2' = y2 + x2 or z2 <= 0 and z2' = z2 and y2' = y2.

z1 > 0 :-
  Inv(x1, y1, z1, x2, y2, z2),
  SchTF(x1, y1, z1, x2, y2, z2), z2 > 0.
z2 > 0 :-
  Inv(x1, y1, z1, x2, y2, z2),
  SchFT(x1, y1, z1, x2, y2, z2), z1 > 0.
SchTF(x1, y1, z1, x2, y2, z2), SchFT(x1, y1, z1, x2, y2, z2), SchTT(x1, y1, z1, x2, y2, z2) :-
  Inv(x1, y1, z1, x2, y2, z2),
  z1 > 0 or z2 > 0.

y1' = y2' :-
  Inv(x1, y1, z1, x2, y2, z2),
  z1 <= 0, z2 <= 0,
  y1' = 2 * y1,
  y2' = 2 * y2.
