// A local declaration initialised by a nondet call inside main.
// Until 2026-09-06 the init-value analysis of lib/c/optimizer.ml asserted that the variable's
// initial value is a closed term; a nondet-initialised variable's "value" is the variable
// itself, so the run died with Assert_failure optimizer.ml:555.  y is a char, so x < 1000 holds.
// Expected: valid.
//@ ltl invariant a: [](AP(x < 1000));
extern char __VERIFIER_nondet_char();
int x;
int main() { int y = __VERIFIER_nondet_char(); x = y; while (1) {} return 0; }
