/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* memmove between overlapping ranges, both directions, and memset with a
   value other than 0 over integer cells. */
#include <string.h>
extern int __VERIFIER_nondet_int(void);
int main(void) {
    int a[8];
    int i;
    for (i = 0; i < 8; i++) a[i] = __VERIFIER_nondet_int();
    int first = a[0];
    memmove(a + 1, a, 7 * sizeof(int));
    if (a[1] != first) return 1;
    memmove(a, a + 1, 7 * sizeof(int));
    if (a[0] != first || a[7] != a[6]) return 2;
    memset(a, 1, 8 * sizeof(int));
    if (a[3] != 0x01010101) return 3;
    memset(a, 255, 2 * sizeof(int));
    if (a[1] != -1) return 4;
    return 0;
}
