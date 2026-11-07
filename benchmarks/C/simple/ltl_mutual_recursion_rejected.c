// f and g call each other: the cycle is refused like direct recursion.
// expected: -p cltl refused (semantic error)
//@ ltl invariant a: <>(AP(x == 1));
int x = 0; int a = 0;
int f(int n) { if (n <= 0) return 0; return g(n - 1); }
int g(int n) { return f(n); }
int main() { a = f(3); x = 1; while (1) {} return 0; }
