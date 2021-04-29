(* 
/* requires piecewise linear ranking */
int main() {
  int x, K;
  while (x != K) {
    if (x > K) {
      x = x - 1;
    } else {
      x = x + 1;
    }
  }
  return 0;
}
*)
I(x,k).
I(x',k) :- I(x,k), x <> k, x > k, x' = x - 1.
I(x',k) :- I(x,k), x <> k, x <= k, x' = x + 1.
WF_R(x,k,x',k) :- I(x,k), x <> k, x > k, x' = x - 1.
WF_R(x,k,x',k) :- I(x,k), x <> k, x <= k, x' = x + 1.