/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 memory-cleanup+reach-error=0 assume-safety=0 */
/* A function atexit registered releases what main left allocated: it runs
   after the return from main and before the check, so nothing is left. */
#include <stdlib.h>
int *g;
int *h;
void cleanup(void) {
    free(g);
    free(h);
}
int main(void) {
    atexit(cleanup);
    g = malloc(sizeof(int));
    h = malloc(4 * sizeof(int));
    *g = 1;
    return 0;
}
