/* @name SelectionSort
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
  while (i < n - 1) {
    int min = i;
    int j = i + 1;
    while (j < n) {
      if (a[j] < a[min]) min = j;
      j = j + 1;
    }
    assert (i != min);
    if (i != min) {
      int tmp = a[i];
      a[i] = a[min];
      a[min] = tmp;
    }
    i = i + 1;
  }
}
