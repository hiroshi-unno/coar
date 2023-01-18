(* 
/* requires piecewise linear ranking */
int main() {
  int x;
  while (x <= 10) 
    x = x + 1;
  return 0;
}
*)
I(x).
I(x') :- I(x), x <= 10, x' = x + 1.
WF_R(x,x') :- I(x), x <= 10, x' = x + 1.