struct S { int a; char b; };
int main(void) {
    struct S s;
    struct S *p = &s;
    char *c = (char *)&s;
    p->a = 1;
    *c = 2;
    return p->a;
}
