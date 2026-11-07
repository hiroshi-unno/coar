#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

/* EXPECT: YES. The block comes from one function and is scanned in another: the returned pointer
   carries its block's bounds, and the argument hands them to the callee, so the assumption ends
   the scan at the block's end. */
int *make(int n) {
    int *a = malloc(n * sizeof(int));
    return a;
}

int count(int *a) {
    int i = 0;
    while (a[i] != 0) {
        i++;
    }
    return i;
}

int main() {
    int n = __VERIFIER_nondet_int();
    if (n < 1) return 0;
    return count(make(n));
}
