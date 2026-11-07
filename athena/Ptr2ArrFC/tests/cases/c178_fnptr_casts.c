/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* Casts between function pointers and other types: compared through
   unsigned long as CIL writes the drivers' comparisons, round trips through
   integers and through void * (held in a structure field, cast back and
   called), a function never equal to an object as void *, and NULL. */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
static int inc(int x) { return x + 1; }
static int dbl(int x) { return 2 * x; }
struct holder { void *fn; void *data; };
int main(void) {
  int (*f)(int) = inc;
  int (*null_fn)(int) = 0;
  printf("%d %d %d\n", (unsigned long)f == (unsigned long)(&inc),
         (unsigned long)f != (unsigned long)(&dbl), (unsigned long)null_fn == 0);
  uintptr_t u = (uintptr_t)f;
  int (*g)(int) = (int (*)(int))u;
  int *obj = malloc(sizeof(int));
  *obj = 5;
  struct holder h = { (void *)&dbl, obj };
  int (*k)(int) = (int (*)(int))h.fn;
  printf("%d %d %d %d\n", g(1), k(3), h.fn != h.data, (void *)null_fn == NULL);
  free(obj);
  return 0;
}
