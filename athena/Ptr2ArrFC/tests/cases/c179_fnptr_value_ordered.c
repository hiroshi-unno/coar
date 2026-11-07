/* Expected: refused (exit status 2), kind function-pointer-value. Function
   pointers compared by size through unsigned long: function numbers are not
   addresses, so the order would not be the input's. */
static int f(void) { return 0; }
static int g(void) { return 1; }
int main(void) {
  int (*a)(void) = f, (*b)(void) = g;
  return (unsigned long)a < (unsigned long)b ? a() : b();
}
