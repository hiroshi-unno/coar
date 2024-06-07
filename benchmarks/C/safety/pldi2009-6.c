/* @name BinarySearch
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
  int low = 0;
  int high = n - 1;
  int e;
  while (low <= high) {
    assume(low <= mid && mid <= high);
    if (a[mid] < e)
      low := mid + 1;
    else if (a[mid] > e)
      high = mid - 1;
    else return;
  }
  assert (forall k. !(0 <= k && k < n) || a[k] != e);
}
