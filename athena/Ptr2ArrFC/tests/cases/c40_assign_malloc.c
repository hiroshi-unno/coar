#include <stdlib.h>
int main(void) {
    int *p;
    p = (int *)malloc(2 * sizeof(int));
    p[1] = 5;
    return p[1];
}
