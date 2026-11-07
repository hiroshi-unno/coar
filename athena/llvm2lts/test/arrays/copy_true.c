extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
int main(void) {
  int a[3] = {7, 8, 9};
  int b[3];
  __builtin_memcpy(b, a, sizeof a);
  __VERIFIER_assert(b[2] == 9);
  return 0;
}
