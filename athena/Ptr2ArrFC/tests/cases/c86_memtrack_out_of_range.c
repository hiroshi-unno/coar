/* p2a-expect: normal=0 memory-safety=79 memory-safety+reach-error=77 memory-cleanup=80 memory-cleanup+reach-error=77 assume-safety=0 */
/* The only pointer left to a heap block points two cells after it: it points
   to no block, so the block is not tracked. */
#include <stdlib.h>
int *g;
int main(void) {
    g = malloc(4 * sizeof(int));
    g[3] = 1;
    g = g + 5;
    return 0;
}
