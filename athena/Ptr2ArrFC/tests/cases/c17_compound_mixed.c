int main(void) {
    int x = 0;
    char *c = (char *)&x;
    int *p = &x;
    *p += 3;
    *c = 1;
    (*p)++;
    return x;
}
