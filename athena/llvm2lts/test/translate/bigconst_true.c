extern unsigned long long __VERIFIER_nondet_ulonglong(void);
extern long long __VERIFIER_nondet_longlong(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
int main(void) {
  unsigned long long x = __VERIFIER_nondet_ulonglong();
  long long y = __VERIFIER_nondet_longlong();
  __VERIFIER_assert(x <= 18446744073709551615ULL);
  __VERIFIER_assert(y <= 9223372036854775807LL);
  __VERIFIER_assert(y >= -9223372036854775807LL - 1);
  return 0;
}
