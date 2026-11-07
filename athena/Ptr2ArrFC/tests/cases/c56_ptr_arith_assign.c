#include <stdlib.h>
int main(void) {
    int *q = malloc(4 * sizeof(int));
    int *p;
    p = q + 1;
    p[2] = 7;
    free(q);
    return 0;
}
