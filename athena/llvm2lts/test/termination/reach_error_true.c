extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_assume(int);
extern void abort(void);
extern void exit(int);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
int main(void) {
  int x = __VERIFIER_nondet_int();
  if (x == 5) reach_error();   /* the execution ends there */
  while (x > 0) x--;
  return 0;
}
