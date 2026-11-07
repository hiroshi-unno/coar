#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

/* EXPECT: YES. The scan of scan.c followed by a free, which the assumption turns into a
   no-op. */
int main() {
    int n = __VERIFIER_nondet_int();
    if (n < 1) return 0;
    int *a = malloc(n * sizeof(int));
    int i = 0;
    while (a[i] != 0) {
        i++;
    }
    free(a);
    return 0;
}
