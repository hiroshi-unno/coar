(* 
/* requires piecewise linear ranking */
void main() {
  int x;
  while (x >= 0)
    x = - 2 * x + 10;
}
*)
I(x).
I(x') :- I(x), x >= 0, x' = -2 * x + 10.
WF_R(x,x') :- I(x), x >= 0, x' = -2 * x + 10.