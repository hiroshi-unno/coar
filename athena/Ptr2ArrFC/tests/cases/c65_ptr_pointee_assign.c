#include <stddef.h>
int main(void) {
    int x = 1;
    int y = 2;
    int *p = &x;
    int **pp = &p;
    p = &y;
    **pp = 5;
    int *q = p;
    *q = *q + 1;
    p = NULL;
    return y;
}
