// f passes its pointer on to g, which writes through it: x becomes 1.
// expected: -p cltl invalid
//@ ltl invariant a: [](AP(x == 0));
int x = 0;
void g(int *q) { (*q) = 1; }
void f(int *p) { g(p); }
int main() { f(&x); while (1) {} return 0; }
