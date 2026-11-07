/* p2a-expect: memory-safety=78 memory-safety+reach-error=77 assume-safety=0 */
/* A block released twice through two copies of its pointer: the second free
   violates valid-free. */
#include <stdlib.h>
int main(void) {
    int *p = malloc(2 * sizeof(int));
    int *q = p;
    p[0] = 1;
    free(p);
    free(q);
    return 0;
}
