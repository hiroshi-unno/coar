extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__nothrow__, __leaf__, __noreturn__));
void reach_error(void) { __assert_fail("0", "t.c", 3U, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error();abort();} } return; }
int main(void) {
  int n = __VERIFIER_nondet_int();
  if (n > 100 || n < 0) return 0;
  int i = 0, x = 0;
  while (i < n) {
    x = x + 2;
    i = i + 1;
  }
  __VERIFIER_assert(x >= 0);
  return 0;
}
