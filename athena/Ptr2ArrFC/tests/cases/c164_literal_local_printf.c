/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* A string literal reaching printf through a local variable that holds
   nothing else, as CIL's temporaries do in the product-lines tasks: the
   argument is replaced by the literal, so the call is printf with a literal
   format; the output is the same characters. */
#include <stdio.h>
int main(void) {
  char const *fmt;
  int bob = 1;
  fmt = "bob: %d\n";
  printf(fmt, bob);
  return 0;
}
