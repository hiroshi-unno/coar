extern int __VERIFIER_nondet_int(void);
extern unsigned int __VERIFIER_nondet_uint(void);
extern void __VERIFIER_assume(int);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
/* __builtin_add_overflow (llvm.sadd.with.overflow) reports an overflow only
   at INT_MAX; outside the wrapping modes the intrinsic is not translated in
   Int. */
int main(void) {
  int x = __VERIFIER_nondet_int();
  int r;
  if (__builtin_add_overflow(x, 1, &r)) {
    __VERIFIER_assert(x == 2147483647 && r == -2147483647 - 1);
  } else {
    __VERIFIER_assert(r == x + 1);
  }
  return 0;
}
