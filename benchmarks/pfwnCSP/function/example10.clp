(* 
/* requires lexicographic linear ranking */
int main() {
  int x1, x2;
  while (x1 != 0 && x2 > 0)
    if (x1 > 0) {
      if (?) {
        x1 = x1 - 1;
        x2 = ?;
      } else
        x2 = x2 - 1;
    } else {
      if (?)
        x1 = x1 + 1;
      else {
        x2 = x2 - 1;
        x1 = ?;
      }
    }
  return 0;
}
*)
I(x1,x2).
I(x1',x2') :- I(x1,x2), x1 <> 0, x2 > 0, x1 > 0, x1' = x1 - 1.
I(x1,x2') :- I(x1,x2), x1 <> 0, x2 > 0, x1 > 0, x2' = x2 - 1.
I(x1',x2) :- I(x1,x2), x1 <> 0, x2 > 0, x1 <= 0, x1' = x1 + 1.
I(x1',x2') :- I(x1,x2), x1 <> 0, x2 > 0, x1 <= 0, x2' = x2 - 1.
WF_R(x1,x2,x1',x2') :- I(x1,x2), x1 <> 0, x2 > 0, x1 > 0, x1' = x1 - 1.
WF_R(x1,x2,x1,x2') :- I(x1,x2), x1 <> 0, x2 > 0, x1 > 0, x2' = x2 - 1.
WF_R(x1,x2,x1',x2) :- I(x1,x2), x1 <> 0, x2 > 0, x1 <= 0, x1' = x1 + 1.
WF_R(x1,x2,x1',x2') :- I(x1,x2), x1 <> 0, x2 > 0, x1 <= 0, x2' = x2 - 1.