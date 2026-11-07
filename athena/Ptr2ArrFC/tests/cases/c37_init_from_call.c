int *id(int *p) { return p; }
int main(void) {
    int x = 0;
    int *p = id(&x);
    *p = 3;
    return x;
}
