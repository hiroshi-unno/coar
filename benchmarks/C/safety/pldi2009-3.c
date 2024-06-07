/* @name ArrayInit
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
  int n;
  int i = 0;
  while (i < n) {
    a[i] = 0;
    i = i + 1;
  }
  assert (forall j. !(0 <= j && j < n) || a[j] = 0);
}
