(* 
/* requires piecewise linear ranking */
void main() {
  int x, y;
  while (x >= 0) {
    if (y <= 50)
      x = x + 1;
    else
      x = x - 1;
    y = y + 1;
  }
}
*)
I(x,y).
I(x',y') :- I(x,y), x >= 0, y <= 50, x' = x + 1, y' = y + 1.
I(x',y') :- I(x,y), x >= 0, y > 50, x' = x - 1, y' = y + 1.
WF_R(x,y,x',y') :- I(x,y), x >= 0, y <= 50, x' = x + 1, y' = y + 1.
WF_R(x,y,x',y') :- I(x,y), x >= 0, y > 50, x' = x - 1, y' = y + 1.