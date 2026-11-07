extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
struct entry { short key; long val; };
struct entry table[3] = { { 1, 10 }, { 2, 20 }, { 3, 30 } };
int main(void) {
  int k = __VERIFIER_nondet_int();
  if (k < 0 || k >= 3) return 0;
  __VERIFIER_assert(table[k].val == 10 * table[k].key);
  return 0;
}
