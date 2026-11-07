extern int __VERIFIER_nondet_int(void);
extern unsigned int __VERIFIER_nondet_uint(void);
extern unsigned char __VERIFIER_nondet_uchar(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
int g = 3;
int main(void) {
  int k = __VERIFIER_nondet_int();
  switch (k) { case 0: g = 10; break; case 1: g = 20; break; default: g = 30; }
  int m = k > 5 ? g : 0;
  __VERIFIER_assert(m == 0 || m == 30);
  return 0;
}
