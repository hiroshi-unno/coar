/* p2a-expect: normal=77 memory-safety=77 memory-safety+reach-error=77 assume-safety=77 */
/* The program only declares reach_error, as older sv-benchmarks tasks do,
   and reaches it without violating memory safety; the differential runner's
   environment stands in for it (status 77). With the split markers the output
   must call it where the program does, and with the reach-error markers under
   its new name, reach_error() being the marker alone (tests/markers.py reads
   the output for this: the status alone cannot tell the two apart). */
extern void reach_error(void);
#include <stdlib.h>
int main(void) {
    int *p = malloc(2 * sizeof(int));
    p[0] = 1;
    p[1] = p[0] + 1;
    if (p[1] == 2) reach_error();
    return 0;
}
