int main(void) {
    int a[6];
    int *p = a;
    int *q = a + 5;
    int n = 0;
    while (p < q) { *p = n; p = p + 1; n++; }
    return (int)(q - p) + n;
}
