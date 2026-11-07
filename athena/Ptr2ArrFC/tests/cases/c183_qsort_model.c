/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* qsort replaced by an insertion sort that calls the comparison function
   through its pointer: the result is sorted and a permutation of the input,
   whatever order equal elements take; the comparison function given
   directly and through a variable. */
#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);
struct item { int key; int val; };
static int cmp_int(const void *a, const void *b) {
  int x = *(const int *)a, y = *(const int *)b;
  return (x > y) - (x < y);
}
static int cmp_item(const void *a, const void *b) {
  const struct item *p = a, *q = b;
  return (p->key > q->key) - (p->key < q->key);
}
int main(void) {
  int a[5];
  int i, sum = 0;
  struct item *its = malloc(4 * sizeof(struct item));
  if (!its) return 0;
  for (i = 0; i < 5; i++) a[i] = __VERIFIER_nondet_int() % 4;
  for (i = 0; i < 4; i++) {
    its[i].key = __VERIFIER_nondet_int() % 3;
    its[i].val = i;
  }
  qsort(a, 5, sizeof(int), cmp_int);
  for (i = 1; i < 5; i++)
    if (a[i - 1] > a[i]) return 1;
  int (*f)(const void *, const void *) = cmp_item;
  qsort(its, 4, sizeof its[0], f);
  for (i = 1; i < 4; i++)
    if (its[i - 1].key > its[i].key) return 2;
  for (i = 0; i < 4; i++) sum += its[i].val;
  if (sum != 6) return 3;
  qsort(a, 0, sizeof(int), cmp_int);
  free(its);
  return 0;
}
