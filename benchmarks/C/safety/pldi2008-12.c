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

main(int i) {
  int even = 0;
  while (i >= 0) {
    if (even == 0)
      i--;
    else
      i++;
    even = 1 - even;
  }
}
