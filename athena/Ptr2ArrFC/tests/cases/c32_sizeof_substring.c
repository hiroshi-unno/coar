int main(void) {
    int e = 1;
    int *p = &e;
    int s = sizeof(*p);
    return s;
}
