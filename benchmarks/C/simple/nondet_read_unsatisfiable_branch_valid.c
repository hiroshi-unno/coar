// y is an unconstrained draw read once, in a condition no integer satisfies:
// the branch is never taken, so it may not become a nondeterministic choice.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(x == 0));
extern int __VERIFIER_nondet_int();
int x = 0;
int y = 0;
int main() { y = __VERIFIER_nondet_int(); if (2 * y == 1) { x = 1; } while (1) {} return 0; }
