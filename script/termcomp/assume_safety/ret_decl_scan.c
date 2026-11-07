#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

/* EXPECT: YES. The scan of scan.c over a block returned by a function and held in a declared
   pointer, which takes the returned bounds. */
int *make(int n) {
    int *a = malloc(n * sizeof(int));
    return a;
}

int main() {
    int n = __VERIFIER_nondet_int();
    if (n < 1) return 0;
    int *p = make(n);
    int i = 0;
    while (p[i] != 0) {
        i++;
    }
    return 0;
}
