int main(void) {
    int a[8];
    int i;
    for (i = 0; i < 8; i++) a[i] = 0;
    int *p = a;
    p[2] = 1;
    return (int)(sizeof(a) / sizeof(a[0])) + a[2];
}
