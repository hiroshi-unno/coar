#include <stdio.h>

int* p;

void create_dangling_pointer() {
    {
        int x = 123;
        p = &x;
    }
}

void dummy_function() {

    int y = 999;
}

int main() {
    create_dangling_pointer();

    dummy_function();

    int z = *p;

    return 0;
}