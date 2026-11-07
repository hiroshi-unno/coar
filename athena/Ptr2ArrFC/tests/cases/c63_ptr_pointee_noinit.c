int main(void) {
    int x = 1;
    int *p;
    int **pp = &p;
    *pp = &x;
    **pp = 5;
    return x;
}
