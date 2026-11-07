int main(void) {
    int x = 5;
    int *p = &x;
    *p = *p + 1;
    return x;
}
