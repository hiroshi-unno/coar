#include <alloca.h>
int main(void) {
    int n = 3;
    int *p = alloca(n * sizeof(int));
    p[0] = 1;
    p[n-1] = 2;
    return p[0] + p[2];
}
