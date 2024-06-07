/* @from Program verification as probabilistic inference
         Sumit Gulwani and Nebojsa Jojic
         POPL 2007 */

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
  y = 50;
  while (x < 100) {
    if (x < 50) {
      x = x + 1;
    } else {
      x = x + 1;
      y = y + 1;
    }
  }
  assert(y == 100);
}
