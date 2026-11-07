/* p2a-expect: normal+check-overflow=77 */
/* 64-bit operations: long long multiplication by the division test, and
   addition near LLONG_MAX; under ILP32 long is 32 bits wide. */
#include <limits.h>
extern int __VERIFIER_nondet_int(void);
int main(void) {
    long long r = 0;
    for (int i = 0; i < 6; i++) {
        long long k = __VERIFIER_nondet_int();
        long long big = (LLONG_MAX / 4) * (k > 0 ? k : 1);   /* k > 4 overflows */
        long l = (long)k * 3 + (LONG_MAX - 40);               /* k > 13 */
        r = (r + big % 7 + l % 5) & 0xffff;
    }
    return (int)(r & 0x7f);
}
