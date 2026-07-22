#include <stdlib.h>

int main() {
    int size = 3;
    int* arr = alloca(size * sizeof(int));

    for (int i = 0; i < size; i++) {
        arr[i] = 100;
    }
    return 0;
}