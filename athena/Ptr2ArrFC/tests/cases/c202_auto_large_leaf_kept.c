/* p2a-expect: normal=0 */
/* m - 2147483648u with m = UINT_MAX stays in range (it is INT_MAX), but the
   leaf m is at least 2^31: the direct route's integer mode may hold m as -1
   (the IR constant i32 -1), and then the difference as -2^31 - 1, outside
   the [-2^31, 2^32) its holders must lie in. --integers=auto must keep the
   reduction. */
#include <limits.h>
int main(void) {
    unsigned m = UINT_MAX;
    unsigned r = m - 2147483648u;
    return r == 2147483647u ? 0 : 1;
}
