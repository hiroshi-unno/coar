#include <stdlib.h>
int main(void) {
    int n = 5;
    int *buf = malloc(n * sizeof(int));
    int *p = buf;
    int i;
    for (i = 0; i < n; i++) *p++ = i;
    return buf[4];
}
