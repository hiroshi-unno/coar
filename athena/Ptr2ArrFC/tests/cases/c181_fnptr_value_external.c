/* Expected: refused (exit status 2), kind function-pointer-value. A function
   pointer's value printed by an external function would print a number. */
#include <stdio.h>
static int f(void) { return 0; }
int main(void) {
  printf("%lx\n", (unsigned long)&f);
  return 0;
}
