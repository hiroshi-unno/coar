/* p2a-expect: normal=0 memory-safety=0 assume-safety=0 */
/* The address of an external function that neither takes nor returns a
   pointer: it is a candidate, called directly. */
extern int __VERIFIER_nondet_int(void);
static int zero(void) { return 0; }
int main(void) {
  int (*src)(void) = __VERIFIER_nondet_int;
  int v = src();
  src = zero;
  return src() + (v - v);
}
