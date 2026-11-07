int main(void) {
    int a[2][3];
    int (*p)[3] = a;
    p[1][2] = 5;
    return a[1][2];
}
