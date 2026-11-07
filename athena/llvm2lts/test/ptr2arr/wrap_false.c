/* Without the reduction the sum would be 256 in Int mode; with it, 0, so the
   error is reachable exactly when the reduction is made. */
extern unsigned char __VERIFIER_nondet_uchar(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
unsigned char __p2a_wrap_u8(unsigned char v) { return v; }
int main(void) {
  unsigned char x = __VERIFIER_nondet_uchar();
  if (x != 255) return 0;
  unsigned char y = __p2a_wrap_u8(x + 1);
  if (y == 0) reach_error();
  return 0;
}
