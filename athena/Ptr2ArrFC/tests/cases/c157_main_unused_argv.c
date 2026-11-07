/* p2a-expect: normal=4 memory-safety=4 memory-safety+reach-error=4 memory-cleanup=4 assume-safety=4 */
/* main declared with argc and argv and reading neither, as many tasks do:
   in a safety mode the pointer parameter of main gets no shadow, since main
   cannot take extra parameters and an unnamed parameter is never
   dereferenced. */
#include <stdlib.h>
int main(int argc, char **argv) {
  int *p = malloc(sizeof(int));
  *p = 4;
  int r = *p;
  free(p);
  return r;
}
