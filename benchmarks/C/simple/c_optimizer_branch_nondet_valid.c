// The same TODO(bug), from the other side: the nondet assignment is inside a branch and the use
// is reachable without it, so the use reads either the nondet char or the default 7.  Both are
// below 1000.  Removing the assignment and substituting an unconstrained nondet would lose the
// char bound and give `invalid`.  Expected: valid.
//@ ltl invariant a: [](AP(x < 1000));
extern char __VERIFIER_nondet_char();
extern int __VERIFIER_nondet_int();
int x;
int main() {
  int y;
  int c = __VERIFIER_nondet_int();
  y = 7;
  if (c > 0) { y = __VERIFIER_nondet_char(); }
  x = y;
  while (1) {}
  return 0;
}
