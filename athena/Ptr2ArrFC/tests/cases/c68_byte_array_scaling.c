int main(void) {
    int a[4];
    int *p = a;
    char *c = (char *)a;
    p[1] = 258;
    c[0] = 1;
    return p[1] + p[0];
}
