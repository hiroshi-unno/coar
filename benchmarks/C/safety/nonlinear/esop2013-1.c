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
  assert(y + y * y == 2 * x);
}

main() {
  int x, y;
  assume(x == 0 && y == 0);
  check_invariant(x, y);
  while (nondet_bool()) {
    y = y + 1;
    x = x + y;
    check_invariant(x, y);
  }
}
