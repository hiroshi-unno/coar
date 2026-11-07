/* Constructs the allow-list admits, with the SV-COMP task functions. */
extern int __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);
extern void __VERIFIER_assume(int);
extern void abort(void);
extern void exit(int);
extern void __assert_fail(const char *, const char *, unsigned int, const char *)
    __attribute__((__noreturn__));
extern int abs(int);
void reach_error() { __assert_fail("0", "accepted.c", 10, "reach_error"); }
void __VERIFIER_assert(int c) { if (!c) { reach_error(); abort(); } }
struct P { int x; int y; };
int g[4] = {1, 2, 3, 4};
static int unused_float(double d) { return (int)(d * 2.0); }
int f(int n) {
  int a[3] = {1, 2, 3};
  int z[10] = {0};
  struct P p = {n, 2};
  int r;
  switch (n) { case 0: r = a[0]; break; case 1: r = z[5]; break; default: r = p.y; }
  return r + g[2];
}
int main(void) {
  int n = __VERIFIER_nondet_int();
  __VERIFIER_assume(n >= 0 && n < 100);
  int v[n + 1];
  for (int i = 0; i <= n; i++) v[i] = i;
  int s;
  if (__builtin_add_overflow(n, 1, &s)) abort();
  if (__VERIFIER_nondet_bool()) exit(0);
  __VERIFIER_assert(f(n) + abs(v[n] - n) >= 0);
  return 0;
}
