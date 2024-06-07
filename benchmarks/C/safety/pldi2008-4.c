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

int mc91(int n) {
  if (n > 100) {
    return n - 10;
  } else {
    return mc91 (mc91 (n + 11));
  }
}

main() {
  int result = mc91(19) + mc91(119);
  assert(result == 200);
}
