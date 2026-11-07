/* p2a-expect: normal+check-overflow=77 */
/* Overflows inside nested expressions, conditions, indices, arguments and
   returns: every operation of a nested expression is checked, in evaluation
   order, and each subexpression is evaluated once. */
#include <limits.h>
extern int __VERIFIER_nondet_int(void);
int a[16];
int f(int x, int y) { return x * y - (x + y); }
int main(void) {
    int u = __VERIFIER_nondet_int(), v = __VERIFIER_nondet_int();
    int w = __VERIFIER_nondet_int();
    a[(u + v + 32) % 16] = f(u, v) * 2;
    if (u * v + w * w > 40) a[0] = 1;
    while (w < 1000000) w = w * 4 + a[(w & 7) + 1] + 1;
    int s = (INT_MAX / 2) + (INT_MAX / 2) + (u > 0 ? u : 1) + 1;
    return (s + a[0]) & 0x7f;
}
