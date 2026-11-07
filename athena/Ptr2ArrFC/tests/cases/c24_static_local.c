int main(void) {
    static int s;
    static int *sp;
    sp = &s;
    *sp = 2;
    return s;
}
