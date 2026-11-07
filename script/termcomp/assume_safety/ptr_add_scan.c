#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

/* EXPECT: YES. The scan of scan.c through a pointer moved by p = p + 1. The moved pointer
   keeps the bounds of the block it points into, so the assumption still ends the scan at the
   block's end. */
int main() {
    int n = __VERIFIER_nondet_int();
    if (n < 1) return 0;
    int *a = malloc(n * sizeof(int));
    int *p = a;
    while (*p != 0) {
        p = p + 1;
    }
    return 0;
}
