extern int __VERIFIER_nondet_int(void);
extern unsigned int __VERIFIER_nondet_uint(void);
extern void __VERIFIER_assume(int);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
/* INT_MAX + 1: undefined in C (the IR's add nsw), so no execution of the C
   program reaches the error (BV, int-wrap-unsigned stop there); without
   wrap-around the sum is 2^31 > 0 (int, int-bitwise); wrapping it as gcc
   -fwrapv gives INT_MIN < 0 (int-wrap-all reaches the error). */
int main(void) {
  int x = __VERIFIER_nondet_int();
  if (x == 2147483647) {
    int y = x + 1;
    __VERIFIER_assert(y > 0);
  }
  return 0;
}
