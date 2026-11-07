extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__nothrow__, __leaf__, __noreturn__));
void reach_error(void) { __assert_fail("0", "t.c", 3U, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
/* clang copies a _Bool parameter into its slot through a zext, so the store is not of the argument itself */
void __VERIFIER_assert(_Bool cond) { if (!cond) { reach_error(); abort(); } }
int main(void) { int x = __VERIFIER_nondet_int(); __VERIFIER_assert(x >= 0 || x < 0); return 0; }
