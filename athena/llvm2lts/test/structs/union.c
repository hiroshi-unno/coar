extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
union U { int i; char c; };
int main(void) {
  union U u;
  u.i = __VERIFIER_nondet_int();
  __VERIFIER_assert(u.c != 3);
  return 0;
}
