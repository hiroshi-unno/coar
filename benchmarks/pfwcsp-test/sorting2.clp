(* 
/* requires piecewise linear ranking */
int main() {
	int x1, x2;
	while (x1 > x2) {
		x1 = x2;
	}
	return 0;
}
*)
I(x1,x2).
I(x1',x2) :- I(x1,x2), x1 > x2, x1' = x2.
WF_R(x1,x2,x1',x2) :- I(x1,x2), x1 > x2, x1' = x2.