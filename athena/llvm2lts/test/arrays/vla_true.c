extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
int main(void) {
  int n = __VERIFIER_nondet_int();
  if (n < 1 || n > 10) return 0;
  int a[n];
  a[n - 1] = 7;
  __VERIFIER_assert(a[n - 1] == 7);
  return 0;
}
