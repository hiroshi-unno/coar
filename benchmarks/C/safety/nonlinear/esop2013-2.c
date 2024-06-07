/* @require nonlinear invariants
   @from A Data Driven Approach for Algebraic Loop Invariants
         Rahul Sharma, Saurabh Gupta, Bharath Hariharan, Alex Aiken, Percy Liang, and Aditya V. Nori
         ESOP 2013 */

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

check_invariant(int x, int y) {
  assert(x * x == y * y);
}

main() {
  int x, y;
  if (x >= 0) y = x;
  else y = -x;
  check_invariant(x, y);
  while (y >= 0 && nondet_bool()) {
    if (x >= y) {
      y = y + 1;
      x = x + 1;
    } else {
      y = y + 1;
      x = x - 1;
    }
    check_invariant(x, y);
  }
}
