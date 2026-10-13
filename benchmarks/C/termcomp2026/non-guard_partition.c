#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int main() {
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();

    while (x >= 0) {
        x = x + y;
        y = y - 1;
    }
    return 0;
}