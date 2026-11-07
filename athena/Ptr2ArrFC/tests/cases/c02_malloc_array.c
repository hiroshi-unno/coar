#include <stdlib.h>
int main(void) {
    int n = 10;
    int *a = malloc(n * sizeof(int));
    int i;
    for (i = 0; i < n; i++) {
        a[i] = i;
    }
    *(a + 2) = 7;
    int s = a[3] + *(a + 2);
    free(a);
    return s;
}
