extern int __VERIFIER_nondet_int(void);
int main(void) {
    int x = 1;
    int y = 2;
    int *p1 = &x;
    int *p2 = &y;
    int *p3 = __VERIFIER_nondet_int() ? &x : &y;
    *p3 = 3;
    return *p1 + *p2;
}
