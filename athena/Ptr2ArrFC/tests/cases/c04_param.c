void set(int *p, int v) { *p = v; }
int get(int *p) { return *p; }
int main(void) {
    int x = 0;
    set(&x, 4);
    int b[3];
    set(b, 1);
    return get(&x) + get(b);
}
