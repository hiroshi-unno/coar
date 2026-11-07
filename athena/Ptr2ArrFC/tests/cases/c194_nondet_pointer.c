/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* A pointer made from a nondeterministic integer: NULL when the integer
   is 0, otherwise a value that points to no object; tests against NULL
   and between copies keep their meaning. */
extern unsigned long __VERIFIER_nondet_ulong(void);
static void *nondet_voidp(void) { return (void *)__VERIFIER_nondet_ulong(); }
struct s { int *p; };
int main(void) {
  int x = 1;
  void *p = nondet_voidp();
  void *q = p;
  struct s st;
  st.p = (int *)__VERIFIER_nondet_ulong();
  if (p != q) return 1;
  if (p != (void *)0 && p == (void *)&x) return 2;
  if (st.p == (int *)0) st.p = &x;
  return 0;
}
