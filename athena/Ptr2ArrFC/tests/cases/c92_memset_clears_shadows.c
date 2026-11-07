/* p2a-expect: normal=0 memory-safety=79 memory-safety+reach-error=77 memory-cleanup=80 memory-cleanup+reach-error=77 assume-safety=0 */
/* memset of a block of pointers to 0: the only pointer to the inner block is
   gone, so it is no longer tracked. */
#include <stdlib.h>
#include <string.h>
int **g;
int main(void) {
    g = malloc(2 * sizeof(int *));
    g[0] = malloc(sizeof(int));
    g[1] = 0;
    memset(g, 0, 2 * sizeof(int *));
    return 0;
}
