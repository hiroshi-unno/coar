int main(void) {
    int x = 1, y = 2;
    int *arr[2];
    arr[0] = &x;
    arr[1] = &y;
    *arr[1] = 5;
    return x + y;
}
