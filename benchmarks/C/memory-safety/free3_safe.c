#include <stdlib.h>

int main() {
    int* arr = malloc(1 * sizeof(int));

    arr[0] = 100;
    free(arr);
    return 0;
}