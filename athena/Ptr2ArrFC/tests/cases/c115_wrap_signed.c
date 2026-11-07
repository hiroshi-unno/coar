/* p2a-expect: normal+wrap-all=110 */
/* Signed arithmetic that relies on two's complement wrap-around (gcc
   -fwrapv): a hash over signed int whose sign and remainder are observed, a
   negation of INT_MIN, a left shift into the sign bit, an increment past
   INT_MAX and a long long product. Without the reductions the mathematical
   reading would see values outside the types' ranges. */
#include <limits.h>
extern int __VERIFIER_nondet_int(void);
int main(void) {
    int h = 17;
    for (int i = 0; i < 20; i++) h = h * 31 + __VERIFIER_nondet_int();
    int n = -(INT_MIN + (__VERIFIER_nondet_int() & 0));  /* wraps to INT_MIN */
    int s = 3 << 30;                                    /* wraps negative */
    long long p = LLONG_MAX;
    p = p * 3 + 7;                                      /* wraps */
    int t = INT_MAX; t++;
    if (n != INT_MIN || s >= 0 || t != INT_MIN) return 1;
    if (p != LLONG_MIN + 4) return 2;   /* 3 * (2^63 - 1) + 7 = 2^64 + 2^63 + 4 */
    int r = h % 50;
    return h < 0 ? 100 + (r < 0 ? -r : r) : 3 + r;
}
