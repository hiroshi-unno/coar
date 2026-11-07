/* Ptr2Arr's --assume-safety cut: __ptr2arr_assume(c) ends the execution when
   c is 0.  The loop runs forever from a negative x, which the cut excludes, so
   the program terminates; read as SV-COMP's __VERIFIER_assume it would not. */
void _Exit(int);
extern int __VERIFIER_nondet_int(void);
void __ptr2arr_assume(int c) { if (!c) _Exit(0); }
int main(void) {
  int x = __VERIFIER_nondet_int();
  __ptr2arr_assume(x >= 0);
  while (x != 0) x--;
  return 0;
}
