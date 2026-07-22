#include <stdlib.h>

int main() {
    int* arr = alloca(2 * sizeof(int)); // allocate memory for 2 integers
    arr[0] = 10;
    arr[1] = 20;

    int* p = arr;
    // even if p goes beyond the range of arr, it won't stop because the condition is "*p != 0"
    while (*p != 0) {
        p++; // keep moving forward, even beyond the allocated 2 integers
    }
    return 0;
}