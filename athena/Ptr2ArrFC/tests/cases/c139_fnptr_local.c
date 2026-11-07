/* p2a-expect: normal=8 memory-safety=8 assume-safety=8 */
/* A function pointer in a local: assigned from function designators (with
   and without &), called with both call syntaxes, compared with another
   function and with NULL, and reassigned in a loop. */
extern int __VERIFIER_nondet_int(void);
static int inc(int x) { return x + 1; }
static int dbl(int x) { return 2 * x; }
static int neg(int x) { return -x; }
int main(void) {
  int (*p)(int) = inc;
  int y = p(1);           /* 2 */
  p = &dbl;
  y = (*p)(y);            /* 4 */
  if (p == dbl) y += 1;   /* 5 */
  if (p != 0 && p != neg) y += 1; /* 6 */
  for (int i = 0; i < 3; i++) {
    p = (i % 2) ? inc : dbl;
    y = p(y) - y + y / 2;  /* 9, 5, 7 */
  }
  int n = __VERIFIER_nondet_int();
  if (n > 0) p = neg; else p = inc;
  int z = p(5);           /* -5 or 6 */
  return y + (z == -5 || z == 6);  /* 8 */
}
