(*
pre(a1 < a2 && b2 < b1)
squaresSum(int a, int b){
  assume(0 < a < b);
  int c=0;
  while (a<b) {c+=a*a; a++;}
  return c;
}
post(c2 < c1)
*)

Inv(a1, b1, c1, a2, b2, c2) :-
  a1 < a2, b2 < b1,
  0 < a1, a1 < b1, 0 < a2, a2 < b2,
  c1 = 0, c2 = 0.

Inv(a1', b1, c1', a2, b2, c2) :-
  Inv(a1, b1, c1, a2, b2, c2),
  SchTF(a1, b1, c1, a2, b2, c2),
  a1 < b1 and c1' = c1 + a1 (** a1*) and a1' = a1 + 1 or a1 >= b1 and c1' = c1 and a1' = a1.
Inv(a1, b1, c1, a2', b2, c2') :-
  Inv(a1, b1, c1, a2, b2, c2),
  SchFT(a1, b1, c1, a2, b2, c2),
  a2 < b2 and c2' = c2 + a2 (** a2*) and a2' = a2 + 1 or a2 >= b2 and c2' = c2 and a2' = a2.
Inv(a1', b1, c1', a2', b2, c2') :-
  Inv(a1, b1, c1, a2, b2, c2),
  SchTT(a1, b1, c1, a2, b2, c2),
  a1 < b1 and c1' = c1 + a1 (** a1*) and a1' = a1 + 1 or a1 >= b1 and c1' = c1 and a1' = a1,
  a2 < b2 and c2' = c2 + a2 (** a2*) and a2' = a2 + 1 or a2 >= b2 and c2' = c2 and a2' = a2.

a1 < b1 :-
  Inv(a1, b1, c1, a2, b2, c2),
  SchTF(a1, b1, c1, a2, b2, c2), a2 < b2.
a2 < b2 :-
  Inv(a1, b1, c1, a2, b2, c2),
  SchFT(a1, b1, c1, a2, b2, c2), a1 < b1.
SchTF(a1, b1, c1, a2, b2, c2), SchFT(a1, b1, c1, a2, b2, c2), SchTT(a1, b1, c1, a2, b2, c2) :-
  Inv(a1, b1, c1, a2, b2, c2),
  a1 < b1 or a2 < b2.

c2 < c1 :- Inv(a1, b1, c1, a2, b2, c2), a1 >= b1, a2 >= b2.

(* hint for non-relational invariant *)
a1 > 0, b2 < b1 :- Inv(a1, b1, c1, a2, b2, c2).
