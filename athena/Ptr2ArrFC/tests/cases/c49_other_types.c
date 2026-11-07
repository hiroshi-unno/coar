int main(void) {
    short s = 1;
    long l = 2;
    unsigned char u = 3;
    short *ps = &s;
    long *pl = &l;
    unsigned char *pu = &u;
    *ps = 4; *pl = 5; *pu = 6;
    return s + (int)l + u;
}
