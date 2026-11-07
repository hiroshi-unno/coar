/* Expected: refused (exit status 2), kind function-pointer-value. A bit test
   on a function pointer's value (an alignment test) reads its address. */
#include <stdint.h>
static int f(void) { return 0; }
int main(void) {
  int (*a)(void) = f;
  return ((uintptr_t)a & 1) ? 1 : a();
}
