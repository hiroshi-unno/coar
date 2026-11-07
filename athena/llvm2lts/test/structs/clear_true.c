extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
struct entry { short key; long val; };
int main(void) {
  struct entry t[8];
  int n = __VERIFIER_nondet_int();
  if (n < 1 || n > 8) return 0;
  __builtin_memset(t, 0, n * sizeof(struct entry));
  __VERIFIER_assert(t[n - 1].key == 0 && t[0].val == 0);
  return 0;
}
