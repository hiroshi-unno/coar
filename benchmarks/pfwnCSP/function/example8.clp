(* 
/* requires piecewise linear ranking */
int main() {
  int x = ?;
  while (x <= 100) {
    if (?)
      x = -2 * x + 2;
    else
      x = -3 * x - 2;
  }
  return 0;
}
*)
I(x).
I(x') :- I(x), x <= 100, x' = -2 * x + 2.
I(x') :- I(x), x <= 100, x' = -3 * x - 2.
WF_R(x,x') :- I(x), x <= 100, x' = -2 * x + 2.
WF_R(x,x') :- I(x), x <= 100, x' = -3 * x - 2.