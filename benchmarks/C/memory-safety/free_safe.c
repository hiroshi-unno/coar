#include <stdlib.h>

int main() {
    int size = 2;
    int* arr = malloc(size * sizeof(int));

    for (int i = 0; i < size; i++) {
        arr[i] = 100;
    }
    free(arr);
    return 0;
}