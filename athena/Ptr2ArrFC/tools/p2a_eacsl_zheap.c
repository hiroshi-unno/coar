/* Linked into the E-ACSL build of the input that p2a_diff.py --uninit check
   uses as its reference: the instrumented code's malloc is redirected here
   (by a macro), so that a heap block starts zero as in the other programs
   the tool runs. E-ACSL's own allocator does not read MALLOC_PERTURB_. The
   fill is not instrumented, so E-ACSL still regards the block as
   uninitialised, which concerns no variable the check reports. */
#include <stdlib.h>
#include <string.h>
void *p2a_zmalloc(size_t n) {
  void *p = malloc(n);
  if (p) memset(p, 0, n);
  return p;
}
