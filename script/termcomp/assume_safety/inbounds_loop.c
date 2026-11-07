#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

/* EXPECT: NO. Never terminates and never leaves its block, so the assumption must not cut
   this execution. */
int main() {
    int *a = malloc(2 * sizeof(int));
    a[0] = 1;
    a[1] = 0;
    while (a[0] > 0) {
        a[1] = a[1] + 1;
    }
    return 0;
}
