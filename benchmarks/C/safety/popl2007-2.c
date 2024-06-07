/* @from Program verification as probabilistic inference
         Sumit Gulwani and Nebojsa Jojic
         POPL 2007 */

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
  int x, m, n;
  x = 0;
  m = 0;
  while (x < n) {
    if (nondet_bool ()) {
      m = x;
    }
    x = x + 1;
  }
  assert((m >= 0 || n <= 0) && (m < n || n <= 0));
}
