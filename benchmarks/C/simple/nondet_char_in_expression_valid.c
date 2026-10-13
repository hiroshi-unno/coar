// A nondeterministic call inside an arithmetic expression.  It was refused by the LTL
// frontend until 2026-09-15 -- not because the call could not be handled, but because the
// addition asked both operands for their sort and nothing can type a call to a function the
// input declares.  expected: valid, and the verdict is the point: a `char` draw cannot
// exceed 127, so `x = __VERIFIER_nondet_char() + 1` keeps `x` far below 1000.  With the
// same program over `__VERIFIER_nondet_int()` the answer is `invalid`, because a 32-bit
// draw is left unbounded by default, so this file also pins that the width of the C type
// reaches the property.
//@ ltl invariant a: [](AP(x < 1000));
extern char __VERIFIER_nondet_char();
int x;
int main() {
  x = __VERIFIER_nondet_char() + 1;
  while (1) {}
  return 0;
}
