extern int __VERIFIER_nondet_int(void);
extern unsigned int __VERIFIER_nondet_uint(void);
extern void __VERIFIER_assume(int);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
/* Bit operations with a constant operand and shifts by a constant: true in
   C for every int and unsigned int, and in every mode that reads them. */
int main(void) {
  int x = __VERIFIER_nondet_int();
  unsigned int u = __VERIFIER_nondet_uint();
  __VERIFIER_assert((x & 7) <= 7);
  __VERIFIER_assert((x >> 1) * 2 + (x & 1) == x);
  __VERIFIER_assert((x | 1) - (x & ~1) == 1);
  if (x < 0) __VERIFIER_assert((x >> 3) < 0);
  __VERIFIER_assert((u >> 31) <= 1);
  __VERIFIER_assert((u & 0xFFu) + (u & ~0xFFu) == u);
  __VERIFIER_assert(((u ^ 5u) ^ 5u) == u);
  return 0;
}
