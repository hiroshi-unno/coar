/* p2a-expect: normal=0 */
/* --integers=auto must keep a reduction that changes the value: u + 1u at
   u = UINT_MAX is 2^32 in the mathematical reading and 0 in C. Without the
   reduction the mathematical reading takes the other branch. */
#include <limits.h>
int main(void) {
    unsigned u = UINT_MAX;
    unsigned v = u + 1u;
    return v == 0u ? 0 : 1;
}
