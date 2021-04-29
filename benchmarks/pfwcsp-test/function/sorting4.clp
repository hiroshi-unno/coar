(* 
/* requires piecewise linear ranking */
int main() {
	int x1, x2, x3, x4;
	while (x1 > x2 || x2 > x3 || x3 > x4) {
		if (x1 > x2) {
			x1 = x2;
			x2 = x1;
		} else if (x2 > x3) {
			x2 = x3;
			x3 = x2;
		} else if (x3 > x4) {
			x4 = x3;
			x3 = x4;
		}
	}
	return 0;
}
*)
I(x1,x2,x3,x4).
I(x1',x2',x3,x4) :- I(x1,x2,x3,x4), x1 > x2, x1 > x2, x1' = x2, x2' = x1'.
I(x1,x2',x3',x4) :- I(x1,x2,x3,x4), x1 > x2, x1 <= x2, x2 > x3, x2' = x3, x3' = x2'.
I(x1,x2,x3',x4') :- I(x1,x2,x3,x4), x1 > x2, x1 <= x2, x2 <= x3, x3 > x4, x4' = x3, x3' = x4'.
I(x1',x2',x3,x4) :- I(x1,x2,x3,x4), x1 <= x2, x2 > x3, x1 > x2, x1' = x2, x2' = x1'.
I(x1,x2',x3',x4) :- I(x1,x2,x3,x4), x1 <= x2, x2 > x3, x1 <= x2, x2 > x3, x2' = x3, x3' = x2'.
I(x1,x2,x3',x4') :- I(x1,x2,x3,x4), x1 <= x2, x2 > x3, x1 <= x2, x2 <= x3, x3 > x4, x4' = x3, x3' = x4'.
I(x1',x2',x3,x4) :- I(x1,x2,x3,x4), x1 <= x2, x2 <= x3, x3 > x4, x1 > x2, x1' = x2, x2' = x1'.
I(x1,x2',x3',x4) :- I(x1,x2,x3,x4), x1 <= x2, x2 <= x3, x3 > x4, x1 <= x2, x2 > x3, x2' = x3, x3' = x2'.
I(x1,x2,x3',x4') :- I(x1,x2,x3,x4), x1 <= x2, x2 <= x3, x3 > x4, x1 <= x2, x2 <= x3, x3 > x4, x4' = x3, x3' = x4'.
WF_R(x1,x2,x3,x4,x1',x2',x3,x4) :- I(x1,x2,x3,x4), x1 > x2, x1 > x2, x1' = x2, x2' = x1'.
WF_R(x1,x2,x3,x4,x1,x2',x3',x4) :- I(x1,x2,x3,x4), x1 > x2, x1 <= x2, x2 > x3, x2' = x3, x3' = x2'.
WF_R(x1,x2,x3,x4,x1,x2,x3',x4') :- I(x1,x2,x3,x4), x1 > x2, x1 <= x2, x2 <= x3, x3 > x4, x4' = x3, x3' = x4'.
WF_R(x1,x2,x3,x4,x1',x2',x3,x4) :- I(x1,x2,x3,x4), x1 <= x2, x2 > x3, x1 > x2, x1' = x2, x2' = x1'.
WF_R(x1,x2,x3,x4,x1,x2',x3',x4) :- I(x1,x2,x3,x4), x1 <= x2, x2 > x3, x1 <= x2, x2 > x3, x2' = x3, x3' = x2'.
WF_R(x1,x2,x3,x4,x1,x2,x3',x4') :- I(x1,x2,x3,x4), x1 <= x2, x2 > x3, x1 <= x2, x2 <= x3, x3 > x4, x4' = x3, x3' = x4'.
WF_R(x1,x2,x3,x4,x1',x2',x3,x4) :- I(x1,x2,x3,x4), x1 <= x2, x2 <= x3, x3 > x4, x1 > x2, x1' = x2, x2' = x1'.
WF_R(x1,x2,x3,x4,x1,x2',x3',x4) :- I(x1,x2,x3,x4), x1 <= x2, x2 <= x3, x3 > x4, x1 <= x2, x2 > x3, x2' = x3, x3' = x2'.
WF_R(x1,x2,x3,x4,x1,x2,x3',x4') :- I(x1,x2,x3,x4), x1 <= x2, x2 <= x3, x3 > x4, x1 <= x2, x2 <= x3, x3 > x4, x4' = x3, x3' = x4'.