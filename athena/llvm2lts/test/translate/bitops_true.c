extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
extern unsigned int __VERIFIER_nondet_uint(void);
int main(void) {
  unsigned x = __VERIFIER_nondet_uint();
  __VERIFIER_assert(__builtin_bswap32(__builtin_bswap32(x)) == x);
  __VERIFIER_assert(__builtin_popcount(x) <= 32);
  if (x != 0) {
    __VERIFIER_assert((x >> __builtin_ctz(x)) & 1);
    __VERIFIER_assert(x >> (31 - __builtin_clz(x)) == 1);
  }
  return 0;
}
