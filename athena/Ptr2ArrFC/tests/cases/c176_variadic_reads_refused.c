/* Expected: refused (exit status 2). A variadic function that reads its
   variable arguments keeps its "..." and is refused as before. */
#include <stdarg.h>
int sum(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int s = 0;
  for (int i = 0; i < n; i++) s += va_arg(ap, int);
  va_end(ap);
  return s;
}
int main(void) { return sum(2, 1, 2) == 3 ? 0 : 1; }
