// A switch in a function inlined at two calls: each copy has its own labels, and a
// return inside a case leaves the function.  pick(0) is 20 and pick(1) is 30.
// expected: -p cltl valid
//@ ltl invariant a: <>(AP(x == 1) && AP(p == 20) && AP(q == 30));
int x = 0; int p = 0; int q = 0;
int pick(int k) { switch (k) { case 0: return 20; case 1: return 30; } return 0; }
int main() { p = pick(0); q = pick(1); x = 1; while (1) {} return 0; }
