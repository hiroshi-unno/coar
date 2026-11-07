/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=80 memory-cleanup+reach-error=77 assume-safety=0 */
/* The only pointer left to a heap block points right after it: SV-COMP's
   rule counts such a pointer, so the block is tracked; it is still left
   allocated. */
#include <stdlib.h>
int *g;
int main(void) {
    g = malloc(4 * sizeof(int));
    g[3] = 1;
    g = g + 4;
    return 0;
}
