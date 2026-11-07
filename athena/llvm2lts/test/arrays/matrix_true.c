extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
int m[2][3];
int main(void) {
  for (int i = 0; i < 2; i++)
    for (int j = 0; j < 3; j++) m[i][j] = i + j;
  __VERIFIER_assert(m[1][2] == 3);
  return 0;
}
