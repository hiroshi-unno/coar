extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_assume(int);
extern void abort(void);
extern void exit(int);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
int f(int n) { if (n <= 0) return 0; return f(n - 1); }
int main(void) { return f(__VERIFIER_nondet_int()); }
