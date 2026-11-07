void inc(int *q) { (*q)++; }
int main(void) {
    int x = 0;
    int *p = &x;
    inc(p);
    return x;
}
