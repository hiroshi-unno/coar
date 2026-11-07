/* The source map of the record on statements outside the input file: the
   function of the header c124_srcmap_header.h is printed, and its
   statements have no input position; a macro used in the middle of a line
   is placed at the macro's name. */
#include "c124_srcmap_header.h"
extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);
#define CHECK(c) if (!(c)) reach_error()
int main(void) {
  int k = count_down(__VERIFIER_nondet_int());
  k = k + 1; CHECK(k == 1);
  return 0;
}
