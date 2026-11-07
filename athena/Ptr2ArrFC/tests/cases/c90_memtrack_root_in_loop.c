/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 memory-cleanup+reach-error=0 assume-safety=0 */
/* A pointer declared in a loop's body of main, which calls a function that
   may abort: --memory-safety makes it an object so that the check at the
   abort sees it, and its block is entered on every iteration. The region
   holds that variable alone and is used as a stack, so 150000 iterations
   fit in arrays of 100000 cells. (The heap block is allocated once: heap
   blocks are never reused, released or not.) */
#include <stdlib.h>
void check(int *p) {
    if (*p < 0) abort();
}
int main(void) {
    int i;
    int *buf = malloc(sizeof(int));
    for (i = 0; i < 150000; i++) {
        int *q = buf;
        *q = i;
        check(q);
    }
    free(buf);
    return 0;
}
