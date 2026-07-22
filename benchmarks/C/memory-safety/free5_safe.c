#include <stdlib.h>

int main() {
    int* arr = malloc(1 * sizeof(int));

    for(int i = 0;i < 1;i++){
        arr[i]= 100;
    }
    free(arr);
    return 0;
}