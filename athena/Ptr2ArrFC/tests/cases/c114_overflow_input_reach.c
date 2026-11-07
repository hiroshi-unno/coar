/* p2a-expect: normal=134 normal+check-overflow=134 */
/* The input's own reach_error (the unreach-call property's) is an ordinary
   function under --check-overflow: it is renamed, and only an overflow calls
   the marker. Seed 1 reaches the input's reach_error. */
#include <limits.h>
#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);
void reach_error(void) { abort(); }
int main(void) {
    int k = __VERIFIER_nondet_int();
    if (k < 100) reach_error();
    return INT_MAX - 10 + k;
}
