/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=80 memory-cleanup+reach-error=77 assume-safety=0 */
/* realloc grows a block of pointers: the pointer it held is copied with its
   shadow, so the inner block is tracked through the new block. */
#include <stdlib.h>
int **g;
int main(void) {
    g = malloc(sizeof(int *));
    g[0] = malloc(sizeof(int));
    g = realloc(g, 2 * sizeof(int *));
    g[1] = 0;
    *g[0] = 1;
    return 0;
}
