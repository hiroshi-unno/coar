/* p2a-expect: normal+check-overflow=77 */
/* Each signed operation the overflow check covers, at the edge of int: the
   first draw chooses the operation, which then overflows unless the second
   draw is negative, so that every operation is the first overflow of some
   execution. */
#include <limits.h>
extern int __VERIFIER_nondet_int(void);
int main(void) {
    int k = __VERIFIER_nondet_int();
    int d = __VERIFIER_nondet_int();
    int z = d < 0 ? 0 : 1;          /* 1: overflow */
    int r = 0;
    switch ((k + 5) % 8) {
    case 0: r = (INT_MAX - 1) + 2 * z; break;            /* add */
    case 1: r = (INT_MIN + 1) - 2 * z; break;            /* sub */
    case 2: r = (65536 * z + 1) * 65536; break;           /* mul */
    case 3: r = -(INT_MIN + 1 - z); break;                /* neg */
    case 4: r = (INT_MIN + 1 - z) / -1; break;            /* div */
    case 5: r = (INT_MIN + 1 - z) % -1; break;            /* rem */
    case 6: r = (1 << 30) << z; break;                    /* shl */
    default: r = (INT_MAX - 2 + z) + (z + d - d) * 2; break; /* nested add */
    }
    return r & 0x7f;
}
