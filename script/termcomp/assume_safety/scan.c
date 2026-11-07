#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

/* EXPECT: YES. Scans a block of n ints for a zero. Every execution that stays in bounds
   terminates: at the latest, a[n] is the first access outside the block. Without the
   assumption the scan may run past the block for ever. */
int main() {
    int n = __VERIFIER_nondet_int();
    if (n < 1) return 0;
    int *a = malloc(n * sizeof(int));
    int i = 0;
    while (a[i] != 0) {
        i++;
    }
    return 0;
}
