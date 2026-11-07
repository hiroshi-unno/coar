/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* Pointers compared through integers as wide as a pointer, as CIL prints
   the comparisons of the Linux drivers: read as comparisons of the
   pointers; the null pointer converted to an integer is 0. */
#include <stdlib.h>
struct node { int v; struct node *next; };
int main(void) {
  struct node a, b;
  struct node *p = &a, *q = &a, *r = &b, *z = NULL;
  long x = 0;
  a.next = &b;
  b.next = NULL;
  if ((unsigned long)p != (unsigned long)q) return 1;
  if ((unsigned long)p == (unsigned long)r) return 2;
  if ((unsigned long)z != (unsigned long)((void *)0)) return 3;
  if ((unsigned long)a.next == (unsigned long)((struct node *)0)) return 4;
  if ((unsigned long)b.next != 0UL) return 5;
  if ((unsigned long)x != (unsigned long)((void *)0)) return 6;
  int n = 0;
  for (struct node *c = &a; (unsigned long)c != (unsigned long)((struct node *)0); c = c->next) n++;
  return n == 2 ? 0 : 7;
}
