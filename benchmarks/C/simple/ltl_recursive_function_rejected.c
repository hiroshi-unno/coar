// A recursive function is refused: calls are inlined, and unfolding a recursive
// one does not terminate.
// expected: -p cltl refused (semantic error)
//@ ltl invariant a: [](AP(x == 1) ==> AP(a == 6));
int x = 0; int a = 0;
int fact(int n) { if (n <= 1) return 1; return n * fact(n - 1); }
int main() { a = fact(3); x = 1; while (1) {} return 0; }
