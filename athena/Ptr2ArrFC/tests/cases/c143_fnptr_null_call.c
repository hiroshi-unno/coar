/* p2a-expect: memory-safety=77 memory-safety+reach-error=77 assume-safety=0 */
/* A call through a null function pointer: undefined in C; an invalid
   dereference in the safety modes. */
static int one(void) { return 1; }
int (*hook)(void);
int main(void) {
  int r = 0;
  if (r) hook = one;
  r = hook();
  return r;
}
