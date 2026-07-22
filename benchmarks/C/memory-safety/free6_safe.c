#include <stdlib.h>

int main() {
    int* arr = malloc(2 * sizeof(int));

    for(int i = 0;i < 2;i++){
        arr[i]= 100;
    }
    free(arr);
    return 0;
}