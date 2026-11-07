/* p2a-expect: memory-safety=81 memory-safety+reach-error=77 memory-cleanup=81 memory-cleanup+reach-error=77 assume-safety=81 */
/* More cells allocated than a region's array holds (100000 by default): the
   output stops at __p2a_region_exhausted() (status 81), which reports
   neither a violation nor its absence; with the reach-error markers it calls
   reach_error() as a violation does. The input itself is safe. */
#include <stdlib.h>
int main(void) {
    int i;
    for (i = 0; i < 3; i++) {
        int *p = malloc(60000 * sizeof(int));
        p[0] = i;
        free(p);
    }
    return 0;
}
