/* p2a-expect: normal=3 memory-safety=3 memory-safety+reach-error=3 assume-safety=3 */
/* srand(time(NULL)) and rand(), as the Juliet tasks seed and draw: a null
   pointer passed to an external function gives it nothing of the program's
   memory, so time(NULL) is not refused. The exit status does not depend on
   the values drawn. */
#include <stdlib.h>
#include <time.h>
int main(void) {
  srand((unsigned int)time(NULL));
  int *a = malloc(4 * sizeof(int));
  int r = rand();
  a[r % 4] = 1;
  int s = r >= 0 ? 3 : 4;
  free(a);
  return s;
}
