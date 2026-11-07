extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
int a[4] = {3, 1, 4, 1};
int main(void) {
  int k = __VERIFIER_nondet_int();
  if (k < 0 || k >= 4) return 0;
  __VERIFIER_assert(a[k] != 4);
  return 0;
}
