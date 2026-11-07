int main(void) {
    int x = 258;
    char *c = (char *)&x;
    int *p = &x;
    *c = 1;
    return *p;
}
