int f(int x) {
    int *p = &x;
    *p = *p + 1;
    return x;
}
int main(void) { return f(3); }
