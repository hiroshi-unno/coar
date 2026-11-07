void first(void) { }
int main(void) {
    int x = 0;
    char *c = (char *)&x;
    int *p = &x;
    *c = 1;
    (*p)++;
    return x;
}
