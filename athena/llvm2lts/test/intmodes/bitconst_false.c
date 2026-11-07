extern int __VERIFIER_nondet_int(void);
extern unsigned int __VERIFIER_nondet_uint(void);
extern void __VERIFIER_assume(int);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
/* x | 4 == 12 for x = 8. */
int main(void) {
  int x = __VERIFIER_nondet_int();
  __VERIFIER_assert((x | 4) != 12);
  return 0;
}
