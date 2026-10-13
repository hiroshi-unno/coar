// A global initialised by a nondet call, read once.  Until 2026-09-06
// the optimizer replaced the read x = y by x = nondet_int() while the range assumption stayed on
// y, so the char bound was lost and [](x < 1000) came out invalid.  Expected: valid.
//@ ltl invariant a: [](AP(x < 1000));
extern char __VERIFIER_nondet_char();
int x;
int y = __VERIFIER_nondet_char();
int main() { x = y; while (1) {} return 0; }
