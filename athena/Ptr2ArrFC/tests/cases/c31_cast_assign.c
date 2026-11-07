#include <stdlib.h>
int main(void) {
    void *v = malloc(8);
    int *q;
    q = (int *)v;
    *q = 1;
    return *q;
}
