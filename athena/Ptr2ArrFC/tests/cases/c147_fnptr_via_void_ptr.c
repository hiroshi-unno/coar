/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* A function pointer cast to a data pointer and back, then called (refused
   until casts to and from other types were read as function numbers): the
   data pointer holds minus the function's number, and the call calls f. */
static int f(void) { return 0; }
int main(void) {
  void *v = (void *)f;
  int (*g)(void) = (int (*)(void))v;
  return g();
}
