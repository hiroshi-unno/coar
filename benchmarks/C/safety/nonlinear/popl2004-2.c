/* @name Generalized Readers-Writers
   @require nonlinear invariants
   @from Non-linear loop invariant generation using Gr\"{o}bner bases
         Sriram Sankaranarayanan, Henny B. Sipma, and Zohar Manna
         POPL 2004 */

extern error();
extern int nondet_bool();

assume(int b) {
  if (!b) {
    assume(b);
  }
}

assert(int b) {
  if (!b) {
    error();
  }
}

main() {
  int r, w, k, c1, c2, k0;
  assume(r == 0 && w == 0 && k == k0);
  while (1) {
    if (nondet_bool()) {
      w = 0;
      r = r + 1;
      k = k - c1;
    } else if (nondet_bool()) {
      r = 0;
      w = w + 1;
      k = k - c2;
    } else if (nondet_bool()) {
      w = 0;
      r = r - 1;
      k = k + c1;
    } else {
      r = 0;
      w = w - 1;
      k = k + c2;
    }
    assert (r * c1 + w * c2 + k == k0 && r * w == 0);
  }
}
