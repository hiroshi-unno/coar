(*
pre(A1 == A2 && len1 == len2)
int arrayInsert(int[] A, int len, int h) {
  int i=0;
  while (i < len && /*A[i] < h*/i != h) i++;
  /*len = shift_array(A, i, 1); A[i] = h;*/
  len = len + 1;
  while (i < len) i++;
  return i;
}
post(i1 == i2)
*)

Inv(b1 : bool, len1, h1, i1, b2 : bool, len2, h2, i2) :-
  len1 = len2, b1, i1 = 0, b2, i2 = 0.

Inv(b1' : bool, len1', h1, i1', b2 : bool, len2, h2, i2) :-
  Inv(b1 : bool, len1, h1, i1, b2 : bool, len2, h2, i2),
  SchTF(b1 : bool, len1, h1, i1, b2 : bool, len2, h2, i2),
  b1 and i1 < len1 and i1 <> h1 and b1' and len1' = len1 and i1' = i1 + 1 or
  b1 and (i1 >= len1 or i1 = h1) and !b1' and len1' = len1 + 1 and i1' = i1 or
  !b1 and i1 < len1 and !b1' and len1' = len1 and i1' = i1 + 1 or
  !b1 and i1 >= len1 and !b1' and len1' = len1 and i1' = i1.
Inv(b1 : bool, len1, h1, i1, b2' : bool, len2', h2, i2') :-
  Inv(b1 : bool, len1, h1, i1, b2 : bool, len2, h2, i2),
  SchFT(b1 : bool, len1, h1, i1, b2 : bool, len2, h2, i2),
  b2 and i2 < len2 and i2 <> h2 and b2' and len2' = len2 and i2' = i2 + 1 or
  b2 and (i2 >= len2 or i2 = h2) and !b2' and len2' = len2 + 1 and i2' = i2 or
  !b2 and i2 < len2 and !b2' and len2' = len2 and i2' = i2 + 1 or
  !b2 and i2 >= len2 and !b2' and len2' = len2 and i2' = i2.
Inv(b1' : bool, len1', h1, i1', b2' : bool, len2', h2, i2') :-
  Inv(b1 : bool, len1, h1, i1, b2 : bool, len2, h2, i2),
  SchTT(b1 : bool, len1, h1, i1, b2 : bool, len2, h2, i2),
  b1 and i1 < len1 and i1 <> h1 and b1' and len1' = len1 and i1' = i1 + 1 or
  b1 and (i1 >= len1 or i1 = h1) and !b1' and len1' = len1 + 1 and i1' = i1 or
  !b1 and i1 < len1 and !b1' and len1' = len1 and i1' = i1 + 1 or
  !b1 and i1 >= len1 and !b1' and len1' = len1 and i1' = i1,
  b2 and i2 < len2 and i2 <> h2 and b2' and len2' = len2 and i2' = i2 + 1 or
  b2 and (i2 >= len2 or i2 = h2) and !b2' and len2' = len2 + 1 and i2' = i2 or
  !b2 and i2 < len2 and !b2' and len2' = len2 and i2' = i2 + 1 or
  !b2 and i2 >= len2 and !b2' and len2' = len2 and i2' = i2.

b1 or i1 < len1 :-
  Inv(b1 : bool, len1, h1, i1, b2 : bool, len2, h2, i2),
  SchTF(b1 : bool, len1, h1, i1, b2 : bool, len2, h2, i2),
  b2 or i2 < len2.
b2 or i2 < len2 :-
  Inv(b1 : bool, len1, h1, i1, b2 : bool, len2, h2, i2),
  SchFT(b1 : bool, len1, h1, i1, b2 : bool, len2, h2, i2),
  b1 or i1 < len1.
SchTF(b1 : bool, len1, h1, i1, b2 : bool, len2, h2, i2),
SchFT(b1 : bool, len1, h1, i1, b2 : bool, len2, h2, i2),
SchTT(b1 : bool, len1, h1, i1, b2 : bool, len2, h2, i2) :-
  Inv(b1 : bool, len1, h1, i1, b2 : bool, len2, h2, i2),
  b1 or i1 < len1 or b2 or i2 < len2.

i1 = i2 :-
  Inv(b1 : bool, len1, h1, i1, b2 : bool, len2, h2, i2),
  !b1, i1 >= len1, !b2, i2 >= len2.
