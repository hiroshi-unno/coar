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

main() {
  int i, j;
  int x = 0;
  int y = 0;
  while (x <= 100) {
    x = x + i;
    y = y + j;
  }
  assert (x >= y);
}
