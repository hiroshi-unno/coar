/* @name Merge
   @from Program verification using templates over predicate abstraction
         Saurabh Srivastava and Sumit Gulwani
         PLDI 2009 */

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
  int[] a;
  int[] b;
  int[] c;
  int i = 0;
  int j = 0;
  int t = 0;
  while (i < n && j < m) {
    if (a[i] <= b [j])
      c[t++] = a[i++];
    else
      c[t++] = b[j++];
  }
  while (i < n)
    c[t++] = a[i++];
  while (j < m)
    c[t++] = b[j++];
  assert (forall k. !(0 <= k && k < t - 1) || c[k] <= c[k + 1]);
}
