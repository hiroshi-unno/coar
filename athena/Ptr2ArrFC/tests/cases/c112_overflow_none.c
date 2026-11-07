/* p2a-expect: normal=0 normal+check-overflow=0 normal+wrap-all=0 */
/* Operations that are not signed overflows and must not be reported:
   unsigned wrap-around, conversions to signed types (implementation-defined,
   not undefined), char and short arithmetic (computed in int), the edges of
   the range reached exactly. */
#include <limits.h>
extern int __VERIFIER_nondet_int(void);
extern unsigned __VERIFIER_nondet_uint(void);
int main(void) {
    unsigned u = UINT_MAX - 1u + (unsigned)(__VERIFIER_nondet_int() & 3); /* wraps */
    int s = (int)u;                    /* conversion */
    char c = 127; c = c + 1;           /* int arithmetic, then conversion */
    short h = SHRT_MAX; h += 5;
    int e = INT_MAX - 1; e = e + 1;    /* INT_MAX exactly */
    int m = INT_MIN + 1; m = m - 1;    /* INT_MIN exactly */
    int n = -(INT_MIN + 1);
    int q = INT_MIN / 1 + (INT_MIN % 2);
    int k = (1 << 30) + ((1 << 30) - 1);
    long long w = (long long)INT_MAX * 2;
    unsigned x = 0u - 1u;
    if (s == 0 && c == 0 && h == 0 && e == 0 && m == 0 && n == 0 && q == 0 && k == 0 && w == 0
        && x == 0)
        return 1;
    return 0;
}
