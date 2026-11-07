int main(void) {
    int a[4];
    int *p = &a[2];
    *p = 1;
    p = &a[1];
    *p = 2;
    return a[1] + a[2];
}
