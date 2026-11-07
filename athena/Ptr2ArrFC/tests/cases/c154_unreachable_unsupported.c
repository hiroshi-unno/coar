/* p2a-expect: normal=7 memory-safety=7 assume-safety=7 */
/* Functions main cannot reach are dropped before the fragment check: the
   first holds a cast of a pointer to an integer and passes a pointer to an
   external function, which would refuse the program, and is never called
   (not static: the front end drops an unused static function by itself).
   A function reached only through a pointer is kept. */
#include <stdlib.h>
extern void ext_takes(int *p);
unsigned long never_called(int *p) {
  ext_takes(p);
  return (unsigned long)p;
}
static int via_pointer(int x) { return x + 2; }
int main(void) {
  int (*f)(int) = via_pointer;
  int *q = malloc(sizeof(int));
  *q = 5;
  int r = f(*q);
  free(q);
  return r;
}
