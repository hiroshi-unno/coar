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
  int d = 0;
  int t = 0;
  int s = 0;
  while (1) {
    if (nondet_bool()) {
      t++;
      s = 0;
    } else if (nondet_bool())
      if (s < 5) {
        d++;
        s++;
      }
  }
}
