#include <stdlib.h>

int main() {
    int size = 3;
    int* arr = malloc(size * sizeof(int));

    arr[0] = 100;
    free(arr);
    return 0;
}