(* 
/* requires piecewise linear ranking */
int main() {
  int x;
  while (x != 0) {
    if (x > 0) {
      x = x - 1;
    } else {
      x = x + 1;
    }
  }
  return 0;
}
*)
I(x).
I(x') :- I(x), x <> 0, x > 0, x' = x - 1.
I(x') :- I(x), x <> 0, x <= 0, x' = x + 1.
WF_R(x,x') :- I(x), x <> 0, x > 0, x' = x - 1.
WF_R(x,x') :- I(x), x <> 0, x <= 0, x' = x + 1.