extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
int pick(int k) {
  int t[3];
  if (k == 0) t[1] = 5;
  return t[1];
}
int main(void) {
  pick(0);
  __VERIFIER_assert(pick(1) == 5);
  return 0;
}
