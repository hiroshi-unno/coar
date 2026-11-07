// The control for the recursion check: f calls h twice, once through g, and
// nothing calls itself, so the program is inlined: f(1) = g(h(1)) + 1 = 4.
// expected: -p cltl valid
//@ ltl invariant a: <>(AP(x == 1) && AP(a == 4));
int x = 0; int a = 0;
int h(int n) { return n + 1; }
int g(int n) { return h(n); }
int f(int n) { int t; t = h(n); return g(t) + 1; }
int main() { a = f(1); x = 1; while (1) {} return 0; }
