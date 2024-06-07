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

bug(int y, n) {
  int x = 0;
  if (y < 9)
    while (x < n) {
      assert (x < 200);
      x = x + y;
    }
  else
    while (x >= 0)
      x++;
}
