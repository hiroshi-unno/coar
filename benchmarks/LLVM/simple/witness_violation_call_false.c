extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__nothrow__, __leaf__, __noreturn__));
void reach_error(void) { __assert_fail("0", "t.c", 3U, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
int f(int a) { return a + 1; }
int main(void) {
  int x = __VERIFIER_nondet_int();
  if (f(x) == 5) reach_error();
  return 0;
}
