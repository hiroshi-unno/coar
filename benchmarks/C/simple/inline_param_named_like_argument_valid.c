// A function whose parameter has the name of the variable passed to it.  The
// arguments are evaluated in the caller's scope before any parameter is bound,
// so f(x) returns 5 and g(b, a) swaps its arguments: y stays 5 and z stays 3.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(y == 5) && AP(z == 3));
int x = 5;
int y = 5;
int a = 2;
int b = 3;
int z = 3;
int f(int x) { return x; }
int g(int a, int b) { return a - b + 2; }
int main() { y = f(x); z = g(b, a); while (1) {} return 0; }
