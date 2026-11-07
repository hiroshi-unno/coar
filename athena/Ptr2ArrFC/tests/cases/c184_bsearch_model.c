/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* bsearch replaced by a search that returns one of the matching elements,
   chosen arbitrarily, or NULL: a found element equals the key, and NULL
   only when no element does; the array given by its start and by its
   address. */
#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);
static const int table[6] = {1, 3, 3, 5, 8, 13};
struct snaps { int n; long v[4]; };
static int cmp_long(const void *a, const void *b) {
  long x = *(const long *)a, y = *(const long *)b;
  return (x > y) - (x < y);
}
static int cmp_int(const void *a, const void *b) {
  int x = *(const int *)a, y = *(const int *)b;
  return (x > y) - (x < y);
}
int main(void) {
  int k = __VERIFIER_nondet_int() % 16;
  int i;
  const int *p;
  p = bsearch(&k, table, 6, sizeof table[0], cmp_int);
  if (p) {
    if (*p != k) return 1;
    if (p < table || p >= table + 6) return 2;
  } else {
    for (i = 0; i < 6; i++)
      if (table[i] == k) return 3;
  }
  struct snaps s = {4, {2, 4, 6, 8}};
  long l = k;
  long *q;
  q = bsearch(&l, &s.v, (unsigned long)s.n, sizeof(long), cmp_long);
  if (q && *q != l) return 4;
  if (!q && (l == 2 || l == 4 || l == 6 || l == 8)) return 5;
  return 0;
}
