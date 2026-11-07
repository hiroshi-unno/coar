#include <stdlib.h>

/* EXPECT: NO. Never terminates, and every access stays in the block a function returned. Bounds
   that the returned pointer did not carry would cut this loop and make it look terminating. */
int *make(void) {
    int *b = malloc(2 * sizeof(int));
    b[0] = 1;
    b[1] = 0;
    return b;
}

int main() {
    int *p = make();
    while (p[0] > 0) {
    }
    return 0;
}
