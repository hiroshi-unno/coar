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

merge(int m1, m2, m3) {
  assert (m1 >= 0 && m2 >= 0);
  int k = 0;
  int i = 0;
  int a[];
  int b[];
  while (i < m1) {
    assert (0 <= k && k < m3);
    a[k++] = b[i++];
  }
  i = 0;
  while (i < m2) {
    assert (0 <= k && k < m3);
    a[k++] = c[i++];
  }
}
