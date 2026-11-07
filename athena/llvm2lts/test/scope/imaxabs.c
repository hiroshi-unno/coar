/* imaxabs, as the Juliet int64_t tasks call it, and the declaration of an
   alias scope an optimised module carries (clang -O0 emits none; the call
   is added by hand).  imaxabs.ll is written by hand. */
#include <inttypes.h>
extern long __VERIFIER_nondet_long(void);
extern void reach_error(void);
int main(void) {
  intmax_t x = __VERIFIER_nondet_long();
  if (imaxabs(x) < 0) reach_error();
  return 0;
}
