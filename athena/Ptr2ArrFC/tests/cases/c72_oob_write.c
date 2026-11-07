/* p2a-expect: memory-safety=77 memory-safety+reach-error=77 assume-safety=0 */
/* A loop that writes one cell past the end of a heap block: the write at
   index 4 violates valid-deref. */
#include <stdlib.h>
int main(void) {
    int i;
    int *a = malloc(4 * sizeof(int));
    for (i = 0; i <= 4; i++)
        a[i] = i;
    return 0;
}
