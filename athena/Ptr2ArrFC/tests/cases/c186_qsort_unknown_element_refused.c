/* Expected: refused (exit status 2), kind function-pointer-external. A
   qsort whose element size is not the size of the type its base points to
   has no known element type: left as an external call taking a function
   pointer, and refused. */
#include <stdlib.h>
static int cmp_pair(const void *a, const void *b) {
  return *(const int *)a - *(const int *)b;
}
int main(void) {
  int a[6] = {5, 0, 3, 1, 4, 2};
  qsort(a, 3, 2 * sizeof(int), cmp_pair);
  return a[0];
}
