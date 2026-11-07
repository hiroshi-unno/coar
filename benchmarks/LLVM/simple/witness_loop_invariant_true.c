extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__nothrow__, __leaf__, __noreturn__));
void reach_error(void) { __assert_fail("0", "t.c", 3U, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
int main(void) {
  int n = __VERIFIER_nondet_int();
  if (n > 100) return 0;
  int i = 0;
  while (i < n) {
    i = i + 1;
  }
  if (i > 100) reach_error();
  return 0;
}
