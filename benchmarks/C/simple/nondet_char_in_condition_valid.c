// A nondeterministic call used inside a *condition*, and as the right-hand side of an
// assignment that is itself the condition -- `if ((fd = __VERIFIER_nondet_char()))`.
// Both were refused by the LTL frontend until 2026-09-15: a comparison asks its operands
// for their sort to pick a predicate symbol, and an assignment used as a condition asks
// the assigned variable for its sort, and nothing can type a call to a function the input
// declares.  expected: valid, and the verdict is what the file checks: a `char` draw lies
// in [-128, 127], so `x` takes a value far below 1000 whichever branch runs.  The width
// bound survives because this frontend declares each `__VERIFIER_nondet_<type>` as an
// ordinary function whose body draws and then assumes the range, so the pass that lifts a
// call out of a condition carries the bound with it.
//@ ltl invariant a: [](AP(x < 1000));
extern char __VERIFIER_nondet_char();
int x;
int fd;
int main() {
  x = 0;
  if ((fd = __VERIFIER_nondet_char())) { x = fd; }
  if (__VERIFIER_nondet_char() > 200) { x = 5000; }
  while (1) {}
  return 0;
}
