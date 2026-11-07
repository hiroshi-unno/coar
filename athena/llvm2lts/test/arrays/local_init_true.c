extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
int main(void) {
  int a[5] = {1, 2, 3, 4, 5};
  int b[6] = {0};
  int k = __VERIFIER_nondet_int();
  if (k < 0 || k >= 5) return 0;
  __VERIFIER_assert(a[k] == k + 1 && b[k] == 0);
  return 0;
}
