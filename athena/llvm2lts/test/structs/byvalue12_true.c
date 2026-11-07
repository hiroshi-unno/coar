extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
struct Q { int a, b, c; };
int sumq(struct Q q) { return q.a + q.b + q.c; }
int main(void) {
  struct Q q = { 1, 2, 3 };
  __VERIFIER_assert(sumq(q) == 6);
  return 0;
}
