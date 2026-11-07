int main(void) {
    int x = 1;
    int *p = &x;
    int **pp = &p;
    **pp = 3;
    *p = **pp + 1;
    return x;
}
