int g;
int *id(int *p) { return p; }
int *getg(void) { return &g; }
int main(void) {
    int x = 0;
    *id(&x) = 5;
    *getg() = 2;
    return x + g;
}
