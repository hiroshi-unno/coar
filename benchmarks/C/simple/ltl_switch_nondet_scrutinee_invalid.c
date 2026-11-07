// A nondeterministic scrutinee can take the value of a case: y = 1 is reachable.
// expected: -p cltl invalid
//@ ltl invariant a: [](AP(y != 1));
extern int __VERIFIER_nondet_int();
int x = 0; int y = 0;
int main() { switch (__VERIFIER_nondet_int()) { case 3: y = 1; break; default: y = 2; } x = 1; while (1) {} return 0; }
