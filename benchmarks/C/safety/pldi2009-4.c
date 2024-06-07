/* @name PartialInit
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
  int n, m;
  int i = 0;
  while (i < n) {
    a[i] = 0;
    i ++;
  }
  assert (forall k. !(0 <= k && k < m) || a[k] = 0);
}
