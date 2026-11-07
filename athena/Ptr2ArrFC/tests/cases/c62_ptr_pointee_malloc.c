#include <stdlib.h>
int main(void) {
    int *p = malloc(2 * sizeof(int));
    int **pp = &p;
    **pp = 5;
    return p[0];
}
