extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__nothrow__, __leaf__, __noreturn__));
void reach_error(void) { __assert_fail("0", "t.c", 3U, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error();abort();} } return; }
int g = 0;
int main(void) {
  int i = 0;
  while (i < 5) { g = g + 2; i = i + 1; }
  __VERIFIER_assert(g == 10);
  return 0;
}
