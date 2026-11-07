/* Expected: refused (exit status 2). The literal is written on one path only, so on the other the variable is
   indeterminate when printf reads it: the argument is not replaced and the
   input is refused (a pointer other than a string literal passed to an
   external function). */
#include <stdio.h>
extern int __VERIFIER_nondet_int(void);
int main(void) {
  char const *fmt;
  if (__VERIFIER_nondet_int()) fmt = "a %d\n";
  printf(fmt, 1);
  return 0;
}
