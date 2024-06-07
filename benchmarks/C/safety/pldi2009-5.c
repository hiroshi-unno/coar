/* @name InitSynthesis
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
  int max, i;
  while (i < n) {
    if (a[max] < a[i]) {
      max = i;
    }
    i ++;
  }
  assert (forall k. !(0 <= k && k < n) || a[max] >= a[k]);
}
