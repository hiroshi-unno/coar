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
  int x, y;
  x = 0;
  y = 0;
  while (1) {
    if (x <= 50) {
      y ++;
    } else {
      y --;
    }
    if (y < 0)
      break;
    x ++;
  }
  assert(x == 102);
}
