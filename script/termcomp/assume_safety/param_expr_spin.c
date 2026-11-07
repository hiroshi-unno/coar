#include <stdlib.h>

/* EXPECT: NO. Never terminates, and every access stays in bounds. The callee's parameter is
   passed an expression, b + 1, whose bounds are b's: with none, every access through a would be
   cut and the loop would look terminating. */
void spin(int *a) {
    while (a[0] > 0) {
    }
}

int main() {
    int *b = malloc(2 * sizeof(int));
    b[0] = 0;
    b[1] = 1;
    spin(b + 1);
    return 0;
}
