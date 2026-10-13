// __VERIFIER_nondet_char() ranges over -128..127 and 127 >= 100, so x < 100 can fail. expected: -p cltl invalid
//@ ltl invariant a: [](AP(x < 100));
extern char __VERIFIER_nondet_char();
int x;
int main() { x = __VERIFIER_nondet_char(); while (1) {} return 0; }
