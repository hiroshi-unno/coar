#include <stdlib.h>

int main() {
    int size = 3;
    int* arr = malloc(size * sizeof(int));

    for (int i = 0; i < size; i++) {
        arr[i] = 100;
    }
    free(arr);
    arr[0] = 1;
    return 0;
}