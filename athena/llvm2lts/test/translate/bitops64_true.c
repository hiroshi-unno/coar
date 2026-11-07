extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
extern unsigned long __VERIFIER_nondet_ulong(void);
extern unsigned short __VERIFIER_nondet_ushort(void);
int main(void) {
  unsigned long y = __VERIFIER_nondet_ulong();
  unsigned short h = __VERIFIER_nondet_ushort();
  __VERIFIER_assert(__builtin_bswap16(h) == (unsigned short)((h << 8) | (h >> 8)));
  __VERIFIER_assert(__builtin_popcountl(y) <= 64);
  if (y != 0) __VERIFIER_assert(__builtin_clzl(y) < 64);
  return 0;
}
