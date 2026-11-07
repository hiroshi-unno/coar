// A char draw returned from a function keeps the range of char.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(y < 1000));
extern char __VERIFIER_nondet_char();
int y = 0;
int f() { return __VERIFIER_nondet_char(); }
int main() { y = f(); while (1) {} return 0; }
