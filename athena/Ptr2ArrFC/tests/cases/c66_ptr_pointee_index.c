int main(void) {
    int a[4];
    int *p = a;
    int **pp = &p;
    p[1] = 3;
    *(p + 2) = 4;
    int *r = &p[3];
    *r = 5;
    return a[1] + a[2] + a[3] + **pp;
}
