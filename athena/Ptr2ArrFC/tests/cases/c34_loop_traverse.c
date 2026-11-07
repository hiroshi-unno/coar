int main(void) {
    int a[10];
    int *p = a;
    while (p < a + 10) {
        *p = 0;
        p++;
    }
    return a[3];
}
