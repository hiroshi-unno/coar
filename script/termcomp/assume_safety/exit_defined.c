#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

/* EXPECT: YES. SV-COMP's idiom makes exit block for ever. A failed memory-safety assumption
   must still end the execution, so it must not go through this exit: if it did, the scan of
   scan.c would be non-terminating here. */
void exit(int s) {
 _EXIT: goto _EXIT;
}

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
