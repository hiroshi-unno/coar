/* p2a-expect: memory-safety=0 memory-safety+reach-error=0 assume-safety=0 */
/* A list built with malloc and never freed (kept reachable from a global, so
   that valid-memtrack holds; memory-cleanup is not expected to): no block of
   its region is ever released, so its accesses need not read the released
   flag, although pointers into the region are stored in it. */
#include <stdlib.h>
struct node { int v; struct node *next; };
struct node *head;
int main(void) {
  struct node *h = 0;
  for (int i = 0; i < 3; i++) {
    struct node *n = malloc(sizeof *n);
    n->v = i;
    n->next = h;
    h = n;
  }
  head = h;
  int s = 0;
  while (h) { s += h->v; h = h->next; }
  return s - 3;
}
