/* p2a-expect: normal=0 memory-safety=79 memory-safety+reach-error=77 memory-cleanup=80 memory-cleanup+reach-error=77 assume-safety=0 */
/* The only pointer to a heap block is overwritten by another allocation: the
   first block is no longer tracked (valid-memtrack), and is left allocated
   at the return from main (valid-memcleanup). */
#include <stdlib.h>
int main(void) {
    int *p = malloc(sizeof(int));
    *p = 1;
    p = malloc(sizeof(int));
    *p = 2;
    free(p);
    return 0;
}
