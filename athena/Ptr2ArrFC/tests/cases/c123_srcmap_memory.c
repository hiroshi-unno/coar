/* The source map of the record in --memory-safety and --memory-cleanup:
   the call of each check is a target with the property of the marker its
   check reaches (valid-deref for an access, valid-free for a release, the
   end checks valid-memtrack or valid-memcleanup), placed at the statement
   or full expression the check guards; the end check at exit is placed at
   the call of exit, the one after main returns at main's return. */
#include <stdlib.h>
#include <string.h>
extern int __VERIFIER_nondet_int(void);
int main(void) {
  int *p = malloc(4 * sizeof(int));
  int n = __VERIFIER_nondet_int();
  p[0] = 1;
  if (p[n & 3] > 0) p[1] = 2;
  memset(p, 0, 2 * sizeof(int));
  if (n == 5) exit(1);
  free(p);
  if (n == 6) free(p);
  return 0;
}
