// f writes through p, which points to the global x, while f has a local of
// the same name: the write reaches the global, so x becomes 1.
// expected: -p cltl invalid
//@ ltl invariant a: [](AP(x == 0));
int x = 0;
void f(int *p) { int x = 5; (*p) = 1; }
int main() { f(&x); while (1) {} return 0; }
