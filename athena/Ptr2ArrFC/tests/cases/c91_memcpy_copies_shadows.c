/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=80 memory-cleanup+reach-error=77 assume-safety=0 */
/* memcpy copies a block of pointers with their shadows: the inner block is
   tracked through the copy after the original block is released, and left
   allocated at the return from main. */
#include <stdlib.h>
#include <string.h>
int **g;
int main(void) {
    int **a = malloc(2 * sizeof(int *));
    a[0] = malloc(sizeof(int));
    a[1] = 0;
    g = malloc(2 * sizeof(int *));
    memcpy(g, a, 2 * sizeof(int *));
    free(a);
    *g[0] = 3;
    return 0;
}
