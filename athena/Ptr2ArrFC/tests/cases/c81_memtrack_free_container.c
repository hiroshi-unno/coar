/* p2a-expect: normal=0 memory-safety=79 memory-safety+reach-error=77 memory-cleanup=80 memory-cleanup+reach-error=77 assume-safety=0 */
/* A heap block holds the only pointer to another; releasing the first loses
   the second (a released block tracks nothing). */
#include <stdlib.h>
struct box { int *item; };
struct box *g;
int main(void) {
    g = malloc(sizeof(struct box));
    g->item = malloc(sizeof(int));
    *g->item = 5;
    free(g);
    g = 0;
    return 0;
}
