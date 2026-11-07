#include <string.h>
#include <stdlib.h>
int main(void) {
    int n = 4;
    char *a = malloc(n);
    memset(a, 0, n);
    return (int)strlen(a);
}
