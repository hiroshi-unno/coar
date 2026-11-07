int main(void) {
    int a[5];
    int *p = a;
    p++;
    *p = 1;
    (*p)++;
    ++p;
    *p++ = 3;
    p--;
    return a[1] + a[2];
}
