/* Expected: refused (exit status 2), kind function-pointer-value (LP64). A
   function pointer converted to an integer narrower than a pointer loses the
   address's high bits; a small function number would not. */
static int f(void) { return 0; }
int main(void) {
  int (*a)(void) = f;
  unsigned int u = (unsigned int)(unsigned long)a;
  unsigned short s = (unsigned short)a;
  return (int)(u - u) + (int)(s - s);
}
