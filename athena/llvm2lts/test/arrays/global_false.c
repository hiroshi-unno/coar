extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
int a[10];
int main(void) {
  for (int i = 0; i < 10; i++) a[i] = i;
  int k = __VERIFIER_nondet_int();
  if (k < 0 || k >= 10) return 0;
  __VERIFIER_assert(a[k] != 7);
  return 0;
}
