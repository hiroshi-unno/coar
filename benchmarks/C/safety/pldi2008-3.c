/* @from Program analysis as constraint solving
         Sumit Gulwani, Saurabh Srivastava, and Ramarathnam Venkatesan
         PLDI 2008
   @used Constraint-Based Invariant Inference over Predicate Abstraction
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

int add(int i, int j) {
  if (i <= 0) {
    ret = j;
  } else {
    int b = i - 1;
    int c = j + 1;
    ret = add(b, c);
  }
  return ret;
}

main() {
  int x, y, result;
  x = 5;
  y = 3;
  result = add(x, y)
  assert(result == 8);
}
