#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);
extern void exit(int __status) __attribute__((__nothrow__, __noreturn__));

/* EXPECT: YES. The input defines __VERIFIER_assume itself, as termCOMP's Di_Stefano_20
   programs do, so the rewritten program must not define it a second time. */
void __VERIFIER_assume(int b) {
  if (!b) exit(0);
}

int main() {
    int n = __VERIFIER_nondet_int();
    __VERIFIER_assume(n >= 1);
    int *a = malloc(n * sizeof(int));
    int i = 0;
    while (a[i] != 0) {
        i++;
    }
    return 0;
}
