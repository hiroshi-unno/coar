extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
void inc(int *p) { *p = *p + 1; }
int main(void) {
  int x = 0;
  inc(&x);
  inc(&x);
  __VERIFIER_assert(x == 2);
  return 0;
}
