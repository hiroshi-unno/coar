extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
void fill(int *p, int n, int v) { for (int i = 0; i < n; i++) p[i] = v; }
int sum(int *p, int n) { int s = 0; for (int i = 0; i < n; i++) s += p[i]; return s; }
int main(void) {
  int a[3];
  fill(a, 3, 2);
  __VERIFIER_assert(sum(a, 3) == 6);
  return 0;
}
