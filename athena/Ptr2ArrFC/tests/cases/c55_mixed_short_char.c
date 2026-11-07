int main(void) {
    short s = 0;
    char *c = (char *)&s;
    short *p = &s;
    *c = 1;
    *p = *p + 1;
    return s;
}
