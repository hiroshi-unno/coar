#include <stdlib.h>
int main(void) {
    void *v = malloc(4 * sizeof(int));
    int *p = (int *)v;
    p[0] = 1;
    return p[0];
}
