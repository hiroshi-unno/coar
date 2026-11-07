struct S { int *p; int v; };
int main(void) {
    int x = 0;
    struct S s;
    s.p = &x;
    *s.p = 1;
    return x;
}
