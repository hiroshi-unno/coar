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

loop(int n, m, x0, y0) {
  assert (x0 < y0);
  int x = x0;
  int y = y0;
  while (x < y) {
    x = x + n;
    y = y + m;
  }
}
