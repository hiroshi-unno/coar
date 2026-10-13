// __VERIFIER_nondet_char() ranges over -128..127,
// so x < 1000 always holds. expected: -p cltl valid (was invalid)
//@ ltl invariant a: [](AP(x < 1000));
extern char __VERIFIER_nondet_char();
int x;
int main() { x = __VERIFIER_nondet_char(); while (1) {} return 0; }
