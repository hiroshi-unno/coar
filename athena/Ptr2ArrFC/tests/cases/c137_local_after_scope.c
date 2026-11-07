/* p2a-expect: memory-safety=77 memory-safety+reach-error=77 memory-cleanup=77 memory-cleanup+reach-error=77 assume-safety=0 */
/* An address-taken local used after the block that declares it ended, in
   the same function: its block is released at the end of the block
   (valid-deref), so the access must check the released flag although no
   pointer to the local leaves the function. */
int main(void) {
  int *p;
  {
    int x = 1;
    p = &x;
  }
  return *p;
}
