#include <stddef.h>
int main(void) {
    int x = 1;
    int *p = NULL;
    if (p == NULL) p = &x;
    *p = 2;
    p = 0;
    return x;
}
