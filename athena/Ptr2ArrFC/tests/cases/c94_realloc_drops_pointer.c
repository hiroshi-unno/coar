/* p2a-expect: normal=0 memory-safety=79 memory-safety+reach-error=77 memory-cleanup=80 memory-cleanup+reach-error=77 assume-safety=0 */
/* realloc shrinks a block of pointers: the pointer past the new length is
   not copied, and the block it pointed to is lost. */
#include <stdlib.h>
int **g;
int main(void) {
    g = malloc(2 * sizeof(int *));
    g[0] = 0;
    g[1] = malloc(sizeof(int));
    g = realloc(g, sizeof(int *));
    return 0;
}
