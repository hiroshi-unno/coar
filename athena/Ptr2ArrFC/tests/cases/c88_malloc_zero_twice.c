/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 memory-cleanup+reach-error=0 assume-safety=0 */
/* Two blocks of no bytes: each has a first index of its own in the block
   table, so releasing both is not a double release. */
#include <stdlib.h>
int main(void) {
    char *p = malloc(0);
    char *q = malloc(0);
    free(p);
    free(q);
    return 0;
}
