#include <stdlib.h>

int main() {
    int size = 1;
    int* arr = malloc(size * sizeof(int));

    free(arr);
    return 0;
}