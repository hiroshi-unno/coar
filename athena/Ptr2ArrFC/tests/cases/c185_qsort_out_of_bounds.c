/* p2a-expect: memory-safety=77 memory-safety+reach-error=77 memory-cleanup=77 assume-safety=0 */
/* qsort told the array has more elements than it has reads past its end:
   valid-deref, as in the input. */
#include <stdlib.h>
static int cmp_int(const void *a, const void *b) {
  int x = *(const int *)a, y = *(const int *)b;
  return (x > y) - (x < y);
}
int main(void) {
  int *a = malloc(3 * sizeof(int));
  if (!a) return 0;
  a[0] = 2; a[1] = 1; a[2] = 0;
  qsort(a, 4, sizeof(int), cmp_int);
  free(a);
  return 0;
}
