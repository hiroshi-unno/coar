extern int __VERIFIER_nondet_int(void);
extern unsigned int __VERIFIER_nondet_uint(void);
extern unsigned char __VERIFIER_nondet_uchar(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
int f(int x) { return x * 2; }
int main(void) {
  int x = __VERIFIER_nondet_int();
  if (x > 1000 || x < -1000) return 0;
  __VERIFIER_assert(f(x) != 7);
  return 0;
}
