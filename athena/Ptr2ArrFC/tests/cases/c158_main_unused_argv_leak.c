/* p2a-expect: normal=4 memory-safety=79 memory-safety+reach-error=77 memory-cleanup=80 assume-safety=4 */
/* c157 with the block lost instead of freed: the memtrack check runs with
   main's unshadowed pointer parameter among the locals. */
#include <stdlib.h>
int main(int argc, char **argv) {
  int *p = malloc(sizeof(int));
  *p = 4;
  int r = *p;
  p = 0;
  return r;
}
