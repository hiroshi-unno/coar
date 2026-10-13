// The upper bound of __VERIFIER_nondet_uint() (2^32 - 1) is not modelled by
// default (unsigned 32-bit results are only x >= 0), so the property is
// reported invalid; with --c-bound-wide-nondets the width is honoured, as the
// LTS frontend does for nondet_uint(), and it is valid.
// expected: -p cltl invalid; with --c-bound-wide-nondets valid
//@ ltl invariant a: [](AP(x <= 4294967295));
extern unsigned int __VERIFIER_nondet_uint();
int x;
int main() { x = __VERIFIER_nondet_uint(); while (1) {} return 0; }
