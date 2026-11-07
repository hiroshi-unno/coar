// y is an unconstrained draw read once, as 2 * y: x is always even.  The read
// may not be replaced by a fresh draw, since 2 * y does not reach every
// integer.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(x != 1));
extern int __VERIFIER_nondet_int();
int x = 0;
int y = 0;
int main() { y = __VERIFIER_nondet_int(); x = 2 * y; while (1) {} return 0; }
