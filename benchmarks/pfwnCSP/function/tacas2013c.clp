(* 
/* requires piecewise linear ranking */
int main() {
  int x1, x2, x3;
  while (x1 > 0 && x2 > 0 && x3 > 0)
    if (?) {
      x1 = x1 - 1;
      x3 = ?;
    } else {
      x1 = ?;
      x2 = x2 - 1;
      x3 = x3 - 1;
    }
  return 0;
}
*)
I(x1,x2,x3).
I(x1',x2,x3') :- I(x1,x2,x3), x1 > 0, x2 > 0, x3 > 0, x1' = x1 - 1.
I(x1',x2',x3') :- I(x1,x2,x3), x1 > 0, x2 > 0, x3 > 0, x2' = x2 - 1, x3' = x3 - 1.
WF_R(x1,x2,x3,x1',x2,x3') :- I(x1,x2,x3), x1 > 0, x2 > 0, x3 > 0, x1' = x1 - 1.
WF_R(x1,x2,x3,x1',x2',x3') :- I(x1,x2,x3), x1 > 0, x2 > 0, x3 > 0, x2' = x2 - 1, x3' = x3 - 1.

