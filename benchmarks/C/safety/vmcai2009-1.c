/* @from Constraint-Based Invariant Inference over Predicate Abstraction
         Sumit Gulwani, Saurabh Srivastava, and Ramarathnam Venkatesan
         VMCAI 2009 */

extern error();

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
  int x, y, m;
  x = 0;
  y = 0;
  while (x < m) {
    x ++;
    y ++;
  }
  assert(y == m);
}
