#include <stdlib.h>

int main() {
    int size = 3;
    int* arr = alloca(size * sizeof(int)); // allocate memory for 3 integers

    // when i is 3 (the 4th iteration of the loop), it will access arr[3]
    for (int i = 0; i <= size; i++) {
        arr[i] = 100; // index out of bounds access, writing to arr[3] which is invalid
    }
    return 0;
}