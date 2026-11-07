int main(void) {
    int a, b;
    int *p, *q;
    p = &a;
    q = &b;
    *p = 1; *q = 2;
    return a + b;
}
