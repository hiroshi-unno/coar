extern int __VERIFIER_nondet_int(void);
extern unsigned int __VERIFIER_nondet_uint(void);
extern void __VERIFIER_assume(int);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
/* 200 converted to signed char is -56 (gcc's modulo conversion, the IR's
   trunc), and -7 / 2 and -7 % 2 round towards zero.  Without wrap-around the
   trunc keeps 200 (int, int-bitwise answer the error reachable). */
int main(void) {
  int v = __VERIFIER_nondet_int();
  __VERIFIER_assume(v == 200);
  signed char c = v;
  int i = c;
  __VERIFIER_assert(i == -56);
  int a = __VERIFIER_nondet_int();
  __VERIFIER_assume(a == -7);
  __VERIFIER_assert(a / 2 == -3 && a % 2 == -1);
  unsigned int w = (unsigned int)a;
  __VERIFIER_assert(w / 2u == 2147483644u);
  return 0;
}
