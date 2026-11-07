extern int __VERIFIER_nondet_int(void);
extern unsigned int __VERIFIER_nondet_uint(void);
extern void __VERIFIER_assume(int);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
/* An element of an uninitialised unsigned char array holds some value of
   its type: the wrapping modes read every loaded value as a value of its
   type; int and int-bitwise read the array's arbitrary contents as
   arbitrary integers (the error is reachable there). */
int main(void) {
  unsigned char b[2];
  b[1] = 7;
  __VERIFIER_assert(b[0] <= 255 && b[1] == 7);
  return 0;
}
