/* @name InsertionSort
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
  int i = 1;
  while (i < n) {
    int j = i - 1;
    val = a[i];
    while (j >= 0 && a[j] > val) {
      a[j + 1] = a[j];
      j = j - 1;
    }
    a[j + 1] = val;
    i = i + 1;
  }
  assert(forall y. exists x. !(0 <= y && y < n) || a[y] = a[x] && 0 <= x && x < n)
}
