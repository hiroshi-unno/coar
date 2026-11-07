/* --integers=auto's reduction of an argument it has shown non-negative,
   written as Ptr2Arr writes it: the identity at the type.  In Int mode it is
   read as one truncating remainder (4300000000 to 5032704). */
extern unsigned int __VERIFIER_nondet_uint(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
unsigned int __p2a_wrapnn_u32(unsigned int v) { return v; }
int main(void) {
  unsigned int x = __VERIFIER_nondet_uint();
  if (x != 4000000000u) return 0;
  unsigned int y = __p2a_wrapnn_u32(x + 300000000u);
  if (y != 5032704u) reach_error();
  return 0;
}
