/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* Unions whose accessed members share one type become structures: a
   pointer stored through one member and read through the other (Juliet's
   _34 tasks), and a union no statement touches inside a structure that is
   copied whole (a spinlock in a driver).  Sizes and the layout of the
   enclosing structure stay as they were. */
#include <stdio.h>
#include <stdlib.h>
typedef union { int *first; int *second; } two_t;
union opaque { char bytes[12]; long long align; };
struct lock { int owner; union opaque word; int count; };
int main(void) {
  two_t u;
  int *p = malloc(sizeof(int));
  *p = 7;
  u.first = p;
  int *q = u.second;
  struct lock a, b;
  a.owner = 1;
  a.count = 2;
  b = a;
  printf("%d %d %d %u %u\n", *q, b.owner, b.count, (unsigned)sizeof(struct lock),
         (unsigned)sizeof(union opaque));
  free(q);
  return 0;
}
