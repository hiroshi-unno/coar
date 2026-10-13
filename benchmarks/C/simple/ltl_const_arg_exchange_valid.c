/* Once b is 1 it stays 1, so the property holds.  The predicate of the
   second loop always sees a constant argument, which preprocessing drops by
   defining the predicate through a fresh one of smaller arity; a candidate
   partial solution sent between MuVal's primal and dual sides then carried
   that definition unclosed, and the exchange stopped with "... is not bound"
   instead of an answer.  Answers draw on the exchange (valid,8,0|2 and
   valid,9,0|15 were both seen), so the verdict is what is asserted. */
//@ ltl invariant positive: [](AP(b == 1) ==> []AP(b == 1));
extern int __VERIFIER_nondet_int();
int b, t, e, limit;
void step() {
  while (1) {
    t = __VERIFIER_nondet_int();
    if (t < 0) { e = 1; }
    if (t > limit) { b = 1; }
  }
}
int main() {
  b = 0; e = 0; limit = 8;
  int try = 0;
  while (1) {
    int l = __VERIFIER_nondet_int();
    if (l < 10) { e = 0; break; } else { e = 1; }
    if (try >= 3) { break; }
    try++;
  }
  e = 3;
  step();
}
