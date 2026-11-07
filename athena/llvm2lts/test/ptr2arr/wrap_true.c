/* --wrap-integers' reductions, written as Ptr2Arr writes them: the identity
   at the type, called where C's conversion wraps.  In Int mode they are read
   as the reduction into the type's range. */
extern unsigned char __VERIFIER_nondet_uchar(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
unsigned char __p2a_wrap_u8(unsigned char v) { return v; }
signed char __p2a_wrap_s8(signed char v) { return v; }
int main(void) {
  unsigned char x = __VERIFIER_nondet_uchar();
  if (x != 255) return 0;
  unsigned char y = __p2a_wrap_u8(x + 1);
  if (y != 0) reach_error();
  unsigned char z = __p2a_wrap_u8(-1);
  if (z != 255) reach_error();
  int w = 200;
  signed char s = __p2a_wrap_s8(w);
  if (s != -56) reach_error();
  return 0;
}
