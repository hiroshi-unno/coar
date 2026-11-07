int *pick(int *a, int *b);
int main(void) {
    int x = 1, y;
    y = 2;
    int *p = &x;
    int *q = &y;
    int *r = pick(p, q);
    return *r;
}
int *pick(int *a, int *b) { return *a > *b ? a : b; }
