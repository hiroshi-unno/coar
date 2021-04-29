(* 
/* requires piecewise linear ranking */
int main() {
  int x1, x2;
  while (x1 <= 10) {
    x2 = 10;
    while (x2 > 1)
      x2 = x2 - 1;
    x1 = x1 + 1;
  }
  return 0;
}
*)
I(x1,x2).
I(x1',x2'') :- I(x1,x2), x1 <= 10, x2' = 10, P(x2',x2''), x1' = x1 + 1.
J(x2') :- I(x1,x2), x1 <= 10, x2' = 10.
J(x2') :- J(x2), x2 > 1, x2' = x2 - 1.
P(x2,x2) :- x2 <= 1.
P(x2,x2'') :- x2 > 1, x2' = x2 - 1, P(x2',x2'').
WF_R(x1,x2,x1',x2'') :- I(x1,x2), x1 <= 10, x2' = 10, P(x2',x2''), x1' = x1 + 1.
WF_S(x2,x2') :- J(x2), x2 > 1, x2' = x2 - 1.
