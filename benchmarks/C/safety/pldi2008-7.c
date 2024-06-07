/* @from Program analysis as constraint solving
         Sumit Gulwani, Saurabh Srivastava, and Ramarathnam Venkatesan
         PLDI 2008 */

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

swap(int x) {
  while (nondet_bool()) {
    if (x == 1)
      x = 2;
    else if (x == 2)
      x = 1;
    assert (x <= 8);
  }
}
